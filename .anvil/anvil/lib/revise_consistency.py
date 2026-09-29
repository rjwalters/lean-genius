"""Deterministic stale-token sweep for the ``*-revise`` lifecycle.

This module is the third member of Anvil's deterministic-checks family
(alongside ``anvil/lib/render_gate.py`` for compiled-PDF gating and
``anvil/lib/marp_lint.py`` for slide-source linting). It
catches a *content-integrity* failure mode that the LLM reviser silently
misses today: when a sourced number on a slide is rewritten between
``<thread>.{N}/deck.md`` and ``<thread>.{N+1}/deck.md`` (e.g. ``$54B+``
collapses to ``$25.9B`` because the prior verdict flagged a market-math
critical), the corresponding figure-script annotation / speaker-notes
phrasing / CSV row often does NOT get updated. The rendered PDF then
ships with the slide body asserting one number and the chart caption
asserting another — exactly the kind of contradiction a sophisticated
investor would catch on first read.

The pattern surfaced on the studio canary in two artifacts in the same
wave (bower.v3 — slide ↔ figure script; draftwell.v3 — slide ↔ speaker
notes); see issue #113 for the full motivation.

Three sub-cases, one primitive
-------------------------------

The reviser-staleness pattern reduces to: *given an old artifact and a
new artifact, find tokens present in the old that were removed; flag
those removed tokens wherever they still appear in companion files.*

That primitive covers all three observed sub-cases:

- (a) ``deck.md`` ↔ ``figures/src/*.{py,csv,mmd}``
- (b) ``deck.md`` ↔ ``speaker-notes.md``
- (c) ``figure.py`` ↔ ``figure.csv``

Design choices
--------------

- **Pure regex, no LLM.** Mirrors ``render_gate`` and ``marp_lint``: the
  deterministic-checks family stays cheap and predictable. The LLM
  reviser *consumes* findings; it does not do the detection.
- **Warn-only.** Findings emit at ``severity="minor"``. False positives
  are possible (a companion can legitimately reference the same number
  for an unrelated reason); the operator/reviser must read each one. A
  ``blocker`` severity would force ``Verdict.BLOCK``, which is too
  strong for v1.
- **``Kind.TOOL_EVIDENCE``.** The sweep IS a tool — it greps files. The
  ``Review`` shape matches ``render_gate.GateResult.to_review`` almost
  verbatim: a single null-scored ``Score`` so the schema validates, one
  ``Finding`` per ``StaleFinding`` with ``tool_calls=[]`` to satisfy
  the kind-required-fields validator, and no ``CriticalFlag`` emission.
- **Empty-findings cleanliness.** ``passed()`` is true on an empty
  result. Skill wiring writes ``_consistency.md`` *only* when findings
  exist, and appends to ``_revision-log.md`` only when written; no noise
  on a clean revision.

Two safety rules eliminate most false positives without an allowlist
--------------------------------------------------------------------

1. **Only removed tokens are candidates.** A token appearing in both
   ``old_source`` and ``new_source`` is *not* flagged, even if it also
   appears in a companion. The source is still asserting that number, so
   the companion's reference is current.
2. **Tokens surviving in ``new_source`` are filtered.** Even among
   "removed" tokens (present in the extracted set difference), if the
   literal token text still appears anywhere in ``new_source``, it is
   *not* flagged. This catches the move-within-file case: the token may
   have shifted slides but is still asserted by the new artifact.

The flag fires only when a companion contains a token that the new
source has *fully dropped*. Operators can extend filtering further via
``ignore_tokens``; the default allowlist is empty.

Public API
----------

- ``sweep(old_source, new_source, companion_files, *, token_set,
  ignore_tokens) -> ConsistencyResult``.
- ``ConsistencyResult`` with ``passed()``, ``to_json()``, and
  ``to_review(version_dir, critic_id)``.
- ``StaleFinding`` — one (companion, line, token) triple.
- ``TokenSet`` / ``DEFAULT_TOKEN_SET`` — regex pack governing what
  counts as a priced-number token. Default set covers money, money
  ranges, percent, and percent ranges (including en-dash ranges; the
  draftwell canary specifically hit ``$25–33M`` with an en-dash).
- ``DEFAULT_COMPANION_GLOBS`` — file globs the caller typically scans.
  Includes ``*.tex`` for forward-compat with LaTeX skills (memo / paper /
  report / installation / proposal / ip-uspto), which are expected to
  adopt the sweep as their own canaries surface. Deck-revise (the v1
  caller) only invokes against ``*.py``, ``*.csv``, ``*.mmd``, and
  ``speaker-notes.md``; ``*.tex`` is dormant until a LaTeX skill wires
  in.
- ``DEFAULT_IGNORE_TOKENS`` — empty ``frozenset()``. Operators extend
  per-thread via the ``ignore_tokens`` parameter.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from anvil.lib.review_schema import (
    Finding,
    Kind,
    Review,
    Score,
)


# Sweep identifier echoed in JSON payloads and the null-scored review
# dimension. Mirrors ``render_gate.GATE_NAME`` usage.
SWEEP_NAME = "revise_consistency"

# Dimension name surfaced on every emitted Finding. Matches the
# deterministic-checks-family convention of using the sweep name as the
# dimension identifier.
DIM_CONSISTENCY = "consistency"


@dataclass(frozen=True)
class TokenSet:
    """Regex pack governing what counts as a 'priced number' token.

    Each field is a Python regex string. The four classes cover the v1
    token vocabulary the canary actually emits; expand by constructing a
    custom ``TokenSet`` and passing it to ``sweep``.

    Both hyphen (``-``) and en-dash (``–``) are accepted in ranges. The
    em-dash (``—``) is rare in number ranges and is intentionally NOT in
    the default set; if a fixture surfaces it, add to ``money_range`` /
    ``percent_range`` rather than introducing a separate class.
    """

    money: str = r"\$[\d,]+(?:\.\d+)?[BMK]?\+?"
    money_range: str = r"\$\d+(?:\.\d+)?[BMK]?[\-–]\$?\d+(?:\.\d+)?[BMK]?"
    percent: str = r"\d+(?:\.\d+)?%"
    percent_range: str = r"\d+(?:\.\d+)?[\-–]\d+(?:\.\d+)?%"

    def patterns(self) -> tuple[str, ...]:
        """Return the regex strings in a stable order.

        Ranges are listed *before* their singleton counterparts so that
        ``re.findall`` picks ``$5-12M`` as a single range token rather
        than two singletons (``$5`` would not match the ``money``
        pattern under the default regex; this ordering is defensive
        against future regex tweaks).
        """
        return (self.money_range, self.percent_range, self.money, self.percent)


# Default token set covering the four canonical classes. Frozen so it can
# be shared safely across calls.
DEFAULT_TOKEN_SET = TokenSet()

# Default companion globs. Includes ``*.tex`` for forward-compat with the
# 5 LaTeX skills (memo, paper, report, installation, proposal, ip-uspto)
# that will adopt this sweep as their own canaries surface. The deck-
# revise v1 caller only invokes against ``*.py``, ``*.csv``, ``*.mmd``,
# and ``speaker-notes.md``; ``*.tex`` is dormant until a LaTeX skill
# wires in. Documenting the dormancy here (and in this module's
# docstring) makes the broader coverage intentional rather than
# speculative.
DEFAULT_COMPANION_GLOBS: tuple[str, ...] = (
    "*.py",
    "*.csv",
    "*.mmd",
    "*.tex",
    "*.md",
)

# Default allowlist. Empty: the two safety rules in ``sweep`` already
# eliminate most false positives without operator help. The
# ``ignore_tokens`` parameter is the per-thread extension point.
DEFAULT_IGNORE_TOKENS: frozenset[str] = frozenset()


# -----------------------------------------------------------------------------
# Result types
# -----------------------------------------------------------------------------


@dataclass
class StaleFinding:
    """One stale-token hit in a companion file.

    Each (companion_file, line, token) triple is its own finding; a
    token that appears on three lines in the same file produces three
    StaleFindings. This is intentional — the operator/reviser may want
    to see every location to decide per-occurrence whether to update or
    decline.
    """

    companion_file: str  # path string (caller-supplied; typically relative to version dir)
    line: int            # 1-indexed line number within the companion
    token: str           # the literal stale token
    rationale: str       # human-readable explanation

    def to_dict(self) -> dict:
        return {
            "companion_file": self.companion_file,
            "line": self.line,
            "token": self.token,
            "rationale": self.rationale,
        }


@dataclass
class ConsistencyResult:
    """Outcome of one ``sweep`` invocation. JSON-serializable + Review-emitter.

    The shape mirrors ``render_gate.GateResult``: ``to_json`` for
    on-disk persistence (the skill wiring writes this to
    ``_consistency.md`` as a structured markdown block), and
    ``to_review`` for the critics-aggregator path
    (``kind=Kind.TOOL_EVIDENCE``, severity ``"minor"``, no
    ``CriticalFlag``s — warn-only).
    """

    old_source: str
    new_source: str
    removed_tokens: frozenset[str]
    findings: list[StaleFinding] = field(default_factory=list)

    def passed(self) -> bool:
        """True when there are no stale-token findings.

        Skill wiring uses this to decide whether to write
        ``_consistency.md`` and append the ``_revision-log.md``
        subsection — empty findings → no noise.
        """
        return not self.findings

    def to_json(self) -> dict:
        """Emit a JSON payload describing the sweep.

        Keys: ``sweep``, ``old_source``, ``new_source``,
        ``removed_tokens`` (sorted for stable output),
        ``findings`` (list of ``StaleFinding`` dicts), ``pass``
        (mirror render_gate's pass key convention).
        """
        return {
            "sweep": SWEEP_NAME,
            "old_source": self.old_source,
            "new_source": self.new_source,
            "removed_tokens": sorted(self.removed_tokens),
            "findings": [f.to_dict() for f in self.findings],
            "pass": self.passed(),
        }

    def to_review(self, *, version_dir: str, critic_id: str) -> Review:
        """Build a typed ``Review`` (``kind=Kind.TOOL_EVIDENCE``).

        Pattern matches ``render_gate.GateResult.to_review`` almost
        verbatim:

        - A single null-scored ``Score`` so ``scores`` is non-empty (the
          schema requires it) but contributes nothing to the aggregated
          total. The sweep owns no rubric dimension — it is a
          deterministic warn-only check.
        - One ``Finding`` per ``StaleFinding`` with ``severity="minor"``,
          ``dimension="consistency"``, ``evidence_span``
          ``<companion>:L<line>``, and ``tool_calls=[]`` to satisfy the
          ``Kind.TOOL_EVIDENCE`` schema validator.
        - No ``CriticalFlag`` emission. Stale-token findings are
          warn-only by contract; a blocker would force ``Verdict.BLOCK``
          which is too strong for v1 (false positives possible).
        """
        scores = [
            Score(
                dimension=SWEEP_NAME,
                score=None,
                max=1,
                justification=(
                    "revise-consistency is a deterministic warn-only "
                    "sweep; owns no rubric dim."
                ),
            )
        ]
        findings: list[Finding] = []
        for sf in self.findings:
            findings.append(
                Finding(
                    severity="minor",
                    dimension=DIM_CONSISTENCY,
                    evidence_span=f"{sf.companion_file}:L{sf.line}",
                    rationale=sf.rationale,
                    suggested_fix=(
                        f"Reconcile {sf.companion_file}:L{sf.line} — "
                        f"either update the stale {sf.token!r} reference "
                        f"to match the new source, or document the "
                        f"decline in _revision-log.md with rationale."
                    ),
                    tool_calls=[],
                )
            )
        return Review(
            schema_version="1",
            kind=Kind.TOOL_EVIDENCE,
            version_dir=version_dir,
            critic_id=critic_id,
            scores=scores,
            findings=findings,
            critical_flags=[],
        )


# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------


def _read_text(path: Path) -> Optional[str]:
    """Read ``path`` as UTF-8 text, returning ``None`` on missing/unreadable.

    Mirrors ``render_gate._scan_placeholders``'s graceful-degrade
    behavior — the sweep's job is to surface stale tokens, not to fail
    when a companion happens to be a binary or has been deleted.
    """
    if not path.exists() or not path.is_file():
        return None
    try:
        return path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        return None


def _extract_tokens(text: str, token_set: TokenSet) -> set[str]:
    """Extract every priced-number token from ``text``.

    Returns a set (deduplicated). The set is used to compute the
    removed-tokens delta between ``old_source`` and ``new_source``.

    Order of patterns matters: ``patterns()`` lists ranges before
    singletons so a ``$5-12M`` range isn't mis-tokenized as two
    independent singletons.
    """
    tokens: set[str] = set()
    for pattern in token_set.patterns():
        for m in re.finditer(pattern, text):
            tokens.add(m.group(0))
    return tokens


def _find_token_occurrences(
    text: str, token: str
) -> list[int]:
    """Return 1-indexed line numbers where ``token`` literally appears in ``text``.

    Uses literal substring matching (not regex) because the token is the
    exact extracted string and we want to surface every occurrence,
    including overlapping ones (rare for priced numbers but possible if
    a token is a prefix of a longer one — e.g. ``$54B`` inside
    ``$54B+``; the substring match flags both lines).
    """
    if not token:
        return []
    hits: list[int] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        if token in line:
            hits.append(lineno)
    return hits


# -----------------------------------------------------------------------------
# Public API: sweep()
# -----------------------------------------------------------------------------


def sweep(
    old_source: Path,
    new_source: Path,
    companion_files: list[Path],
    *,
    token_set: TokenSet = DEFAULT_TOKEN_SET,
    ignore_tokens: Optional[frozenset[str]] = None,
) -> ConsistencyResult:
    """Compute removed tokens between ``old_source`` and ``new_source``,
    then scan each companion for residual occurrences.

    Parameters
    ----------
    old_source:
        Prior-version source artifact (e.g. ``<thread>.{N}/deck.md``).
    new_source:
        Just-written source artifact (e.g. ``<thread>.{N+1}/deck.md``).
    companion_files:
        Explicit list of companion paths to scan. Caller resolves globs
        (e.g. ``<thread>.{N}/figures/src/*.{py,csv,mmd}``) before
        passing in. Missing files are silently skipped (graceful
        degrade).
    token_set:
        Regex pack governing what counts as a priced-number token.
        Defaults to ``DEFAULT_TOKEN_SET`` covering money, money ranges,
        percent, and percent ranges (hyphen + en-dash).
    ignore_tokens:
        Per-call allowlist. Any token in this set is skipped even if
        removed. Defaults to ``DEFAULT_IGNORE_TOKENS`` (empty).

    Returns
    -------
    ConsistencyResult
        With ``findings`` empty (clean) or populated (one entry per
        (companion, line, token) triple).

    Notes
    -----
    Two safety rules eliminate most false positives without an
    allowlist:

    1. **Only removed tokens are candidates.** Tokens present in both
       ``old_source`` and ``new_source`` are not flagged.
    2. **Tokens surviving in ``new_source`` are filtered.** Even among
       "removed" tokens (set difference of extracted tokens), if the
       literal token text still appears anywhere in ``new_source``, it
       is not flagged (it may have moved within the file).

    Missing source files are tolerated: if ``old_source`` doesn't exist,
    the removed-tokens set is empty and the result is a clean pass; if
    ``new_source`` doesn't exist, no surviving-tokens filter runs but
    the result is still well-defined (every removed token is a
    candidate).
    """
    ignore = ignore_tokens if ignore_tokens is not None else DEFAULT_IGNORE_TOKENS

    old_path = Path(old_source)
    new_path = Path(new_source)

    old_text = _read_text(old_path) or ""
    new_text = _read_text(new_path) or ""

    old_tokens = _extract_tokens(old_text, token_set)
    new_tokens = _extract_tokens(new_text, token_set)

    # Safety rule #1: only tokens removed in the delta are candidates.
    removed = old_tokens - new_tokens

    # Apply the allowlist before the surviving-tokens filter so the
    # operator can suppress a token regardless of whether it survived.
    removed = frozenset(t for t in removed if t not in ignore)

    # Safety rule #2: filter tokens that survive (as literal substrings)
    # anywhere in new_source. _extract_tokens uses regex; this filter is
    # an exact substring check so a token whose regex no longer matches
    # in new_source but whose text still appears (e.g. inside a larger
    # composite token) is still suppressed.
    surviving = frozenset(t for t in removed if t in new_text)
    candidates = removed - surviving

    findings: list[StaleFinding] = []
    for companion in companion_files:
        companion_path = Path(companion)
        body = _read_text(companion_path)
        if body is None:
            continue
        for token in sorted(candidates):
            for lineno in _find_token_occurrences(body, token):
                findings.append(
                    StaleFinding(
                        companion_file=str(companion),
                        line=lineno,
                        token=token,
                        rationale=(
                            f"{new_path.name} no longer contains "
                            f"{token!r}; {Path(companion).name} still "
                            f"does — likely stale reference."
                        ),
                    )
                )

    return ConsistencyResult(
        old_source=str(old_path),
        new_source=str(new_path),
        removed_tokens=candidates,
        findings=findings,
    )


__all__ = [
    "SWEEP_NAME",
    "DIM_CONSISTENCY",
    "TokenSet",
    "DEFAULT_TOKEN_SET",
    "DEFAULT_COMPANION_GLOBS",
    "DEFAULT_IGNORE_TOKENS",
    "StaleFinding",
    "ConsistencyResult",
    "sweep",
]
