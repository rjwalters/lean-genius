"""Deterministic no-fabrication invariant gate for `anvil:deslop` (issue #922).

Spun out of #919 (mining report: `docs/research/919-ai-humanizer-mining.md`,
bucket c.1). `blader/humanizer` states an explicit no-fabrication invariant
— a rewrite must not contain any fact, name, number, date, quote, or
citation absent from the source text — but checks it only with an LLM
self-audit question at revise time ("Does the rewrite state any fact,
name, number, date, or citation that isn't in the source?"). That is a
judgment call the model can simply forget to make.

This module is the **deterministic** version: a post-revise diff gate that
compares iteration N against iteration N+1 and names, mechanically, every
numeral / proper-noun / citation-shaped token that appears in N+1 but not
in N (or in a resolved voice-grounding doc, or an explicit operator
carve-out). It composes the diff-based "did this revision introduce
content that wasn't there before" precedent `anvil/lib/parity.py`
established for a structurally similar problem (deck↔memo hard-claim
drift, issue #200/#215/#317) — same extract-tokens-then-set-diff shape —
without importing from it, since parity's tokens/normalization are tuned
for a *sibling-artifact* comparison (deck vs. memo, both anvil-authored)
rather than this module's *iteration-vs-iteration* comparison over prose
anvil does not own the provenance of.

**Advisory, not a hard block** — matching `anvil/lib/rhetoric_lint.py`'s
"advisory by contract" posture. `commands/deslop.md` step 3e runs this
check right after writing iteration N+1 and carries the findings forward
into the *next* iteration's step 3c critique (the same way `lint_body`'s
findings are evidence the critique step must cite or explicitly decide not
to act on) — a **named, deterministic** finding, not something only caught
if the LLM happens to notice it in a self-audit question.

Detection surface (deliberately conservative — false-negative-tolerant,
matching every other Anvil lint's calibration posture)
--------------------------------------------------------------------------
- **Numerals**: any digit run, optionally with a leading ``$`` or a
  trailing ``%``, thousands separators, or a decimal point — covers plain
  counts, dates, percentages, and money figures in one extractor (a bare
  ``2026`` and a ``$50M`` figure are both "a number that wasn't there").
- **Proper nouns**: capitalized multi-word sequences (2-5 consecutive
  Title-Case words) not present in N or any resolved voice-grounding doc.
  A single capitalized word is NOT flagged — that would fire on every
  sentence-initial capital in ordinary prose; the multi-word bound is the
  same false-positive-tolerance trade-off `anvil/lib/parity.py` makes with
  its length-bounded acronym extractor.
- **Citation-shaped tokens**: bracketed numeric refs (``[12]``, ``[3, 4]``),
  bare URLs (``https://...``), and quoted strings (``"..."`` / ``'...'``).

Exclusion scope (composes with `rhetoric_lint`, does not duplicate it)
--------------------------------------------------------------------------
Both iterations are masked through `anvil.lib.rhetoric_lint.scannable_lines`
before extraction — the exact fenced-code / HTML-comment / inline-code
exclusion `lint_rhetoric` already applies, exposed as a public entry point
for this second consumer (issue #922) rather than re-implemented here. A
code sample embedded in ingested prose (e.g. a README fragment showing a
CLI invocation with a version number) can never register as an
"introduced" token.

Exception paths (mirrors `blader/humanizer`'s "swapping a vague claim for
a specific one is allowed only when the specific comes from the source or
the user" carve-out)
--------------------------------------------------------------------------
1. **Voice-grounding docs**: pass the resolved `ResolvedVoiceDoc.paths`
   (or bare path strings) from `orchestrate.voice_context()` as
   ``voice_doc_paths=``. A token that appears in a resolved
   STYLE_GUIDE/VOCABULARY/VALUES/corpus doc is legitimate specificity the
   consumer already declared, not a fabrication — it is added to the
   allowed set exactly like a token already present in iteration N.
2. **Explicit operator-supplied detail**: pass ``extra_allowed_tokens=``
   for a specific the operator hands the agent directly outside the
   ingested source/voice docs (e.g. dictating a real figure to swap in for
   a vague claim). Documented, not auto-derived — there is no upstream
   Sources block or evidence-grade taxonomy in `deslop`'s ingest-untrusted-
   prose posture to infer this from automatically.

What this module deliberately does NOT do: decide whether a flagged token
is actually a fabrication. A proper noun sequence can legitimately survive
a revise pass unchanged (then it is in N already and is never flagged) or
be a real quote the operator dictated (the extra-allowed-tokens carve-out).
This module only names, deterministically, what changed — the critique
pass in `commands/deslop.md` step 3c is where the judgment call happens,
same division of labor as `lint_body`/`RhetoricLintResult`.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Sequence, Union

from anvil.lib.rhetoric_lint import scannable_lines

# ---------------------------------------------------------------------------
# Finding kinds
# ---------------------------------------------------------------------------

KIND_NUMERAL = "numeral"
KIND_PROPER_NOUN = "proper_noun"
KIND_CITATION = "citation"


# ---------------------------------------------------------------------------
# Token extractors
# ---------------------------------------------------------------------------

# Numerals: 2026, 50%, $50M, 3.14, 1,000. Word-boundary-ish guards (negative
# look-around on alnum) keep a mid-identifier digit run (e.g. inside a URL,
# which the citation extractor already owns) from double-counting as a bare
# numeral — the citation extractors run first per line and the numeral
# extractor is intentionally left un-guarded against overlap since the
# de-dupe below keys on (kind, token), not on character span.
_NUMERAL_RE = re.compile(r"(?<![\w$])\$?\d[\d,]*(?:\.\d+)?%?(?!\w)")

# Proper nouns: 2-5 consecutive Title-Case words. Deliberately excludes a
# single capitalized word (fires on every sentence-initial capital
# otherwise) — see module docstring's false-positive-tolerance rationale.
_PROPER_NOUN_RE = re.compile(
    r"\b[A-Z][A-Za-z'’-]*(?:\s+[A-Z][A-Za-z'’-]*){1,4}\b"
)

# Citation-shaped tokens: bare URLs, bracketed numeric refs, quoted strings.
_URL_RE = re.compile(r"\bhttps?://\S+")
_BRACKET_REF_RE = re.compile(r"\[\d+(?:\s*,\s*\d+)*\]")
_QUOTED_RE = re.compile(r'"[^"\n]{2,300}"|\'[^\'\n]{2,300}\'')


def _normalize_token(token: str) -> str:
    """Collapse internal whitespace so a token that wraps a hard line
    break still compares equal to its unwrapped form. No case-folding —
    exact surface form is what "wasn't there before" means here."""
    return re.sub(r"\s+", " ", token.strip())


# ---------------------------------------------------------------------------
# Hit extraction
# ---------------------------------------------------------------------------


@dataclass
class _Hit:
    kind: str
    token: str
    line: int  # 1-based


def _extract_hits(text: str) -> List[_Hit]:
    """Extract every numeral / proper-noun / citation hit from ``text``.

    Applies :func:`anvil.lib.rhetoric_lint.scannable_lines` first so
    fenced code, HTML comments, and inline code spans never contribute a
    hit — the same exclusion scope `lint_rhetoric` uses.
    """
    hits: List[_Hit] = []
    for line_idx, line in enumerate(scannable_lines(text), start=1):
        for pattern, kind in (
            (_URL_RE, KIND_CITATION),
            (_BRACKET_REF_RE, KIND_CITATION),
            (_QUOTED_RE, KIND_CITATION),
            (_NUMERAL_RE, KIND_NUMERAL),
            (_PROPER_NOUN_RE, KIND_PROPER_NOUN),
        ):
            for m in pattern.finditer(line):
                token = _normalize_token(m.group(0))
                if token:
                    hits.append(_Hit(kind=kind, token=token, line=line_idx))
    return hits


def _load_allowed_tokens_from_docs(
    voice_doc_paths: Sequence[Union[str, Path]],
) -> set[str]:
    """Read each resolved voice-grounding doc and return its token set.

    Graceful by contract (mirrors every other Anvil lint's "a broken
    consumer declaration must not sink the check" posture): an unreadable
    or missing path is silently skipped rather than raising — the caller
    forwarded whatever `orchestrate.voice_context()` resolved, and a stale
    path there is `resolve_voice_docs`'s concern to surface, not this
    gate's.
    """
    allowed: set[str] = set()
    for raw in voice_doc_paths:
        path = Path(raw)
        try:
            content = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        allowed.update(h.token for h in _extract_hits(content))
    return allowed


# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------


@dataclass
class NoFabricationFinding:
    """One token introduced in the revised iteration with no traceable
    origin in the prior iteration, a resolved voice-grounding doc, or an
    explicit operator carve-out."""

    kind: str  # "numeral" | "proper_noun" | "citation"
    token: str
    line: int  # 1-based line number in the REVISED (N+1) text
    message: str

    def to_dict(self) -> dict:
        return {
            "kind": self.kind,
            "token": self.token,
            "line": self.line,
            "message": self.message,
        }


@dataclass
class NoFabricationResult:
    """Aggregate result of one N -> N+1 no-fabrication diff."""

    findings: List[NoFabricationFinding] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.findings)

    def by_kind(self, kind: str) -> List[NoFabricationFinding]:
        return [f for f in self.findings if f.kind == kind]

    def to_summary(self) -> dict:
        """Shape suitable for embedding in a `findings.md` / rationale
        block, mirroring the ``to_summary()`` convention used by
        `RhetoricLintResult` and `anvil.lib.parity.LintResult`."""
        return {
            "total": self.total,
            "numerals": [f.token for f in self.by_kind(KIND_NUMERAL)],
            "proper_nouns": [f.token for f in self.by_kind(KIND_PROPER_NOUN)],
            "citations": [f.token for f in self.by_kind(KIND_CITATION)],
            "findings": [f.to_dict() for f in self.findings],
        }


def _build_message(kind: str, token: str, line: int) -> str:
    if kind == KIND_NUMERAL:
        return (
            f"Numeral `{token}` (line {line}) appears in the revised text but "
            f"not in the prior iteration, any resolved voice-grounding doc, "
            f"or an explicit operator-supplied detail. Verify it traces to "
            f"the source or the operator before keeping it — an invented "
            f"figure is a no-fabrication violation, not ordinary rewording."
        )
    if kind == KIND_PROPER_NOUN:
        return (
            f"Name-like phrase `{token}` (line {line}) appears in the "
            f"revised text but not in the prior iteration, any resolved "
            f"voice-grounding doc, or an explicit operator-supplied detail. "
            f"Confirm it isn't an invented name/entity before keeping it."
        )
    return (
        f"Citation-shaped token `{token}` (line {line}) appears in the "
        f"revised text but not in the prior iteration, any resolved "
        f"voice-grounding doc, or an explicit operator-supplied detail. A "
        f"rewrite must not manufacture a quote, URL, or reference the "
        f"source never carried."
    )


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------


def diff_no_fabrication(
    prior_text: str,
    revised_text: str,
    *,
    voice_doc_paths: Optional[Sequence[Union[str, Path]]] = None,
    extra_allowed_tokens: Optional[Sequence[str]] = None,
) -> NoFabricationResult:
    """Diff ``prior_text`` (iteration N) against ``revised_text`` (N+1).

    Returns a :class:`NoFabricationResult` naming every numeral /
    proper-noun / citation-shaped token that appears in ``revised_text``
    but is absent from ``prior_text``, every resolved voice-grounding doc
    in ``voice_doc_paths``, and ``extra_allowed_tokens`` — the two
    documented exception paths (see module docstring). A token present in
    ANY of those three sources is allowed and never flagged, regardless of
    which kind it was extracted as.

    Pure function of its inputs — reads ``voice_doc_paths`` from disk (best
    effort, never raises) but does not touch ``prior_text`` /
    ``revised_text``'s origin. Order-preserving, de-duplicated by
    ``(kind, token)`` — a token repeated on several lines of the revised
    text is reported once, at its first occurrence.
    """
    prior_hits = _extract_hits(prior_text)
    revised_hits = _extract_hits(revised_text)

    allowed: set[str] = {h.token for h in prior_hits}
    if voice_doc_paths:
        allowed.update(_load_allowed_tokens_from_docs(voice_doc_paths))
    if extra_allowed_tokens:
        allowed.update(_normalize_token(t) for t in extra_allowed_tokens if t)

    findings: List[NoFabricationFinding] = []
    seen: set[tuple[str, str]] = set()
    for hit in revised_hits:
        if hit.token in allowed:
            continue
        key = (hit.kind, hit.token)
        if key in seen:
            continue
        seen.add(key)
        findings.append(
            NoFabricationFinding(
                kind=hit.kind,
                token=hit.token,
                line=hit.line,
                message=_build_message(hit.kind, hit.token, hit.line),
            )
        )
    return NoFabricationResult(findings=findings)


__all__ = [
    "KIND_NUMERAL",
    "KIND_PROPER_NOUN",
    "KIND_CITATION",
    "NoFabricationFinding",
    "NoFabricationResult",
    "diff_no_fabrication",
]
