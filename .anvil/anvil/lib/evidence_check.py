"""Quoted-evidence verifier for critic scoring tables (issue #464).

Fifth member of the deterministic-checks family (alongside
``anvil/lib/render_gate.py``, ``anvil/lib/marp_lint.py``,
``anvil/lib/revise_consistency.py``, ``anvil/lib/scorecard_check.py``,
and ``anvil/lib/numeric_consistency.py``). It enforces the
**quoted-evidence discipline** from the draftwell survey: every
per-dimension score in a critic's ``scoring.md`` must cite verbatim
text from the document under review, so a lazy critic cannot emit
plausible-sounding scores ungrounded in the actual draft (the same
failure class the studio canary hit with VLM critics scoring figures
they had not decoded).

The snippet-side contract lives in ``anvil/lib/snippets/rubric.md``
§"Dimension scoring guidance" rule 1: each dimension's justification
embeds at least one verbatim quote from the reviewed body — wrapped in
double quotes, followed by a human-facing location anchor — and a dim
scored at full weight MAY substitute the by-absence marker phrase
``no instance of <X> found`` (absence of defects has no quotable span).
This module is the deterministic verifier for the quote half of that
rule; anchors are judgment-scope and are NOT validated here.

Deterministic subset (pure stdlib — no LLM, no new deps)
--------------------------------------------------------

1. **Scorecard parsing** — two scorecard shapes feed the SAME
   classifier:

   - **Table (``human-verdict``)** — reuses
     ``anvil/lib/critics.py::parse_memo_scoring_table`` on the
     ``| # | Dimension | Weight | Score | Justification |`` row shape.
   - **Machine-summary (``machine-summary``)** — the two ip skills
     (``ip-uspto``, ``ip-uspto-provisional``) write a *partial* scorecard
     inside ``_summary.md``. The canonical shape the commands instruct
     and the examples carry is the SAME markdown table
     (``| # | Dimension | Weight | Score | Justification |``), so the
     machine-summary path reuses ``parse_memo_scoring_table`` too (issue
     #536). A fenced ``json`` ``dimensions`` block (issue #496) is also
     accepted when present — :func:`parse_machine_summary_dimensions`
     parses each dimension key to ``null`` (un-owned) or an object with
     ``score`` + ``justification`` (+ optional ``weight``) — but no
     shipped command doc or example emits it, so it is forward-compat /
     legacy and the table fallback fires in practice. The classifier,
     normalization, span+elision matching, and the by-absence marker are
     all scorecard-source-agnostic — only the parser differs, and the
     machine-summary route tries JSON first then the table.

   Rows with a ``null`` / ``n/a`` / ``-`` score are skipped entirely:
   a critic that does not own a dimension (the partial-scorecard rule
   in ``snippets/critics.md``) owes no evidence for it. Dispatch is by
   the sibling ``_meta.json`` ``scorecard_kind`` discriminator (NOT a
   hardcoded skill name) so the routing generalizes to any future
   machine-summary skill.

2. **Quoted-span extraction** — text inside straight (``"…"``) or
   curly (``“…”``) double quotes within the justification cell.
   Spans shorter than :data:`MIN_QUOTE_CHARS` characters (after
   normalization) are ignored — trivial / idiomatic quoting ("why
   now", "soft target") is not evidence. The cutoff is a heuristic
   module constant, tuned on canary signal.

3. **Matching** — both the span and the body are normalized (curly →
   straight quotes, em/en dashes and ``--`` / ``---`` hyphen runs
   folded to one canonical dash token, markdown emphasis characters
   ``*`` / ``_`` / backticks stripped, whitespace collapsed) and the
   span must appear as a **case-sensitive substring** of the
   normalized body. LaTeX bodies (``main.tex``) are matched against
   the ``.tex`` source verbatim — reviewers read source, so quotes
   must match source (the symmetric dash fold keeps ``--`` / ``---``
   dash markup in ``.tex`` source self-consistent with quotes typed
   either way).

   **Ellipsis elision** (issue #478) is permitted *inside a span*:
   a span containing ``...`` / ``…`` is split on the elision markers
   and matches when every fragment (each ≥ :data:`MIN_QUOTE_CHARS`
   normalized chars — the per-fragment floor that blocks
   ``"the ... market"``-style trivial stitching) appears verbatim in
   the body **in document order** (advancing-cursor match: fragment N
   must start after fragment N−1 ends) **and** all fragments fall
   within :data:`ELISION_WINDOW_CHARS` normalized characters of the
   first fragment's match start (the anti-stitching proximity window —
   two distant real fragments must not stitch into fabricated
   meaning). Fragment matching is greedy-leftmost (each fragment binds
   to its first in-order occurrence; no backtracking retry — a
   documented v1 simplification). A span that matches the body as a
   plain substring (e.g. it quotes a *literal* ellipsis present in the
   body) passes without fragment splitting; leading/trailing ellipses
   degrade to plain single-fragment matching. Elision handling lives
   in :func:`span_matches_body`, NOT in :func:`normalize` — folding
   ellipses in the normalizer would corrupt body text containing
   literal ellipses.

4. **Per-justification classification** (this ordering is
   load-bearing — it tolerates calibration-suffix quotes from
   ``rubric_overrides`` / artifact-type overlays that legitimately
   quote rubric prose, not body text):

   1. ≥1 extracted span matches the body → **pass**.
   2. ``score == weight`` AND the by-absence marker
      (``no instance of <X> found``) is present → **pass**
      (ceiling-by-absence contract).
   3. ≥1 span extracted but NONE matches the body →
      **major finding**: :data:`FABRICATED_EVIDENCE` — the quote does
      not appear verbatim in the reviewed body.
   4. No spans at all → **minor (advisory) finding**:
      :data:`MISSING_EVIDENCE`.

Where findings flow (issue #464 curation)
-----------------------------------------

**No sidecar is written.** Two consumption modes only:

1. **Write-time self-check** (the memo pilot): the reviewer runs this
   verifier against its staging-dir ``scoring.md`` (via ``--scoring``)
   alongside the existing ``scorecard_check`` invocation. Missing-
   evidence findings → the reviewer adds the quote before the sidecar
   lands; fabricated-evidence findings → hard self-check failure: the
   reviewer re-derives the justification from the actual body. Same
   deterministic-correction posture as the scorecard arithmetic gate.
2. **Standalone post-hoc CLI** over legacy review dirs → advisory
   reporting only — never mutates, never gates.

A ``--write-review`` critic-sibling mode (a critic reviewing critics)
is explicitly OUT of scope — the aggregator is untouched.

CLI entry-point
---------------

``python -m anvil.lib.evidence_check <version_dir> [--scoring <path>]
[--body <path>]``

Without ``--scoring``, discovers every critic-sibling
``<version_dir>.<critic>/scoring.md`` (table) and
``<version_dir>.<critic>/_summary.md`` (machine-summary JSON — issue
#496) next to the version dir (the critic-sibling glob per
``snippets/critics.md``), routing each by its sibling ``_meta.json``
``scorecard_kind``; with ``--scoring``, checks exactly that one file
(the reviewer's staging-dir self-check path — a ``_summary.md`` path
routes to the machine-summary parser, a ``scoring.md`` to the table
parser). The body file is auto-detected inside the version dir:
``<slug>.md`` (the #295 slug-echo shape — memo, essay) first, then the
per-skill fixed names in :data:`FIXED_BODY_NAMES` order: ``main.tex``
(paper), ``report.md`` (report), ``deck.md`` (deck, slides),
``proposal.tex`` (proposal), ``installation.tex`` (installation),
``datasheet.tex`` (datasheet), ``spec.tex`` (ip-uspto,
ip-uspto-provisional) — issue #475. (``anvil.lib.body_resolution``'s
default ``fallback_names`` resolves only ``<slug>.md`` / ``main.tex``;
this module passes its own extended :data:`FIXED_BODY_NAMES` chain
instead.) ``--body PATH`` overrides
discovery for adopted-in-place legacy threads whose entry point isn't
``<slug>.md``/:data:`FIXED_BODY_NAMES` (e.g. a ``paper.tex``); the
resolved (portfolio-relative) path is what ``body_path`` records.
``.tex`` bodies match verbatim with the symmetric dash fold — no
per-format normalization branch.

Writes a JSON summary to stdout. Exit codes: ``0`` clean, ``1`` one or
more findings, ``2`` invocation error (missing version dir, body file,
or ``--scoring`` file) — the #462/#338/#337 convention.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Tuple

from anvil.lib.body_resolution import record_body_path, resolve_body_path
from anvil.lib.critics import parse_memo_scoring_table


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CHECK_NAME = "evidence_check"
"""Check identifier echoed in JSON payloads."""

MIN_QUOTE_CHARS = 15
"""Minimum normalized length for a quoted span to count as evidence.

Heuristic cutoff that skips trivial / idiomatic quoting ("why now",
"soft target"). Ship-as-constant, tune on canary signal (issue #464
risk note). Doubles as the per-fragment floor for ellipsis-elided
spans (issue #478): each elided fragment must independently clear it.
"""

ELISION_WINDOW_CHARS = 500
"""Proximity window for ellipsis-elided spans (issue #478).

All fragments of an elided span must fall within this many normalized
characters of the first fragment's match start — the anti-stitching
constraint that prevents two distant real fragments from being
stitched into fabricated meaning. Ship-as-constant, tune on canary
signal (the MIN_QUOTE_CHARS posture).
"""

# Finding codes (stable identifiers; consumers grep for these).
FABRICATED_EVIDENCE = "fabricated_evidence"
MISSING_EVIDENCE = "missing_evidence"
EMPTY_SCORECARD = "empty_scorecard"

# Finding severities. Fabricated evidence is a major finding (the gate
# this module exists for); missing evidence is a minor advisory.
SEVERITY_MAJOR = "major"
SEVERITY_MINOR = "minor"

# Ceiling-by-absence marker: a dim scored at full weight MAY substitute
# "no instance of <X> found" for a quote — absence of defects has no
# quotable span. Tolerant of plural ("no instances of ... found") and
# case; the <X> placeholder is bounded to keep the match same-sentence.
_ABSENCE_MARKER_RE = re.compile(
    r"\bno\s+instances?\s+of\s+[^.;|]{1,120}?\bfound\b",
    re.IGNORECASE,
)

# Quoted spans: straight double quotes or curly double quotes. Spans
# never contain a pipe (justifications live in single table cells) or a
# newline.
_QUOTED_SPAN_RES: Tuple[re.Pattern, ...] = (
    re.compile(r'"([^"\n|]+)"'),
    re.compile("“([^“”\n|]+)”"),
)

# Markdown emphasis characters stripped by normalization.
_EMPHASIS_CHARS_RE = re.compile(r"[*_`]")

_CURLY_FOLD = {
    "“": '"',
    "”": '"',
    "‘": "'",
    "’": "'",
}

# Dash variants folded to one canonical token by normalization (issue
# #478): em dash, en dash, and 2-3 hyphen runs (`---` matched before
# `--` via the greedy quantifier — order matters). Symmetric folding
# means verbatim em-dash quotes still pass, `--`-typed quotes match
# `—` bodies, and `--scoring`-style literals stay self-consistent
# (both sides fold identically). Single hyphens are NOT folded —
# compound words ("single-customer") are not dashes.
_DASH_FOLD_RE = re.compile(r"—|–|-{2,3}")
_DASH_CANONICAL = "—"

# Elision markers splitting a quoted span into fragments (issue #478):
# ASCII three-or-more dots or the Unicode horizontal ellipsis. Lives
# in span matching, NOT in normalize() — folding ellipses in the
# normalizer would corrupt body text containing literal ellipses.
_ELISION_MARKER_RE = re.compile(r"\.\.\.+|…")


# ---------------------------------------------------------------------------
# Normalization + extraction
# ---------------------------------------------------------------------------


def normalize(text: str) -> str:
    """Normalize text for span-vs-body matching.

    Folds curly quotes to straight, folds dash variants (``—`` / ``–``
    / ``---`` / ``--``) to one canonical dash token (issue #478),
    strips markdown emphasis characters (``*``, ``_``, backticks),
    collapses all whitespace runs to single spaces, and strips. Case
    is preserved — matching is case-sensitive by contract (a quote is
    verbatim or it is not evidence). Ellipses are deliberately NOT
    folded here — elision is span-side semantics handled in
    :func:`span_matches_body`, and folding it here would corrupt body
    text containing literal ellipses.
    """
    for curly, straight in _CURLY_FOLD.items():
        text = text.replace(curly, straight)
    text = _DASH_FOLD_RE.sub(_DASH_CANONICAL, text)
    text = _EMPHASIS_CHARS_RE.sub("", text)
    return re.sub(r"\s+", " ", text).strip()


def extract_quoted_spans(text: str) -> List[str]:
    """Extract candidate evidence spans from a justification cell.

    Returns the raw (un-normalized) inner text of every straight- or
    curly-double-quoted span whose **normalized** length is at least
    :data:`MIN_QUOTE_CHARS`. Shorter spans are dropped entirely — they
    neither satisfy nor violate the evidence rule.
    """
    spans: List[str] = []
    for pattern in _QUOTED_SPAN_RES:
        for m in pattern.finditer(text):
            inner = m.group(1)
            if len(normalize(inner)) >= MIN_QUOTE_CHARS:
                spans.append(inner)
    return spans


def has_absence_marker(text: str) -> bool:
    """``True`` when the justification carries the by-absence marker."""
    return bool(_ABSENCE_MARKER_RE.search(text))


def _elided_fragments_match(
    fragments: List[str], normalized_body: str
) -> bool:
    """In-order, windowed match of an elided span's fragments.

    Every fragment must clear the per-fragment :data:`MIN_QUOTE_CHARS`
    floor, appear in the body in document order (advancing cursor:
    fragment N starts after fragment N−1 ends), and end within
    :data:`ELISION_WINDOW_CHARS` of the first fragment's match start.
    Matching is greedy-leftmost: each fragment binds to its first
    in-order occurrence, with no backtracking retry when a later
    occurrence would have satisfied the window — a documented v1
    simplification (issue #478 curation).
    """
    if any(len(f) < MIN_QUOTE_CHARS for f in fragments):
        return False
    cursor = 0
    first_start: Optional[int] = None
    for fragment in fragments:
        idx = normalized_body.find(fragment, cursor)
        if idx == -1:
            return False
        if first_start is None:
            first_start = idx
        elif idx + len(fragment) > first_start + ELISION_WINDOW_CHARS:
            return False
        cursor = idx + len(fragment)
    return True


def span_matches_body(span: str, normalized_body: str) -> bool:
    """Case-sensitive substring match of a normalized span in the body.

    The caller pre-normalizes the body once (via :func:`normalize`) and
    passes it here for each span.

    Ellipsis elision (issue #478): a span that does not match as a
    plain substring but contains ``...`` / ``…`` markers is split into
    fragments, and matches when every fragment is ≥
    :data:`MIN_QUOTE_CHARS`, appears in the body in document order,
    and falls within :data:`ELISION_WINDOW_CHARS` of the first
    fragment's match start (see :func:`_elided_fragments_match`). The
    plain-substring check runs first, so a quote of a *literal* body
    ellipsis still passes verbatim. Leading/trailing ellipses leave a
    single fragment and degrade to plain single-fragment matching
    (no per-fragment floor beyond the extraction-time cutoff).
    """
    normalized_span = normalize(span)
    if normalized_span in normalized_body:
        return True
    fragments = [
        f.strip() for f in _ELISION_MARKER_RE.split(normalized_span)
    ]
    fragments = [f for f in fragments if f]
    if not fragments or fragments == [normalized_span]:
        return False  # no elision markers — plain match already failed
    if len(fragments) == 1:
        # Leading/trailing ellipsis only: plain single-fragment match.
        return fragments[0] in normalized_body
    return _elided_fragments_match(fragments, normalized_body)


# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------


@dataclass
class EvidenceFinding:
    """One quoted-evidence finding against a scoring.md justification."""

    code: str          # fabricated_evidence | missing_evidence
    severity: str      # "major" | "minor"
    dimension: str     # rubric dimension name from the table row
    scoring_path: str  # which scoring.md the row came from
    score: Optional[int]
    weight: int
    spans_extracted: int
    message: str

    def to_dict(self) -> dict:
        return {
            "code": self.code,
            "severity": self.severity,
            "dimension": self.dimension,
            "scoring_path": self.scoring_path,
            "score": self.score,
            "weight": self.weight,
            "spans_extracted": self.spans_extracted,
            "message": self.message,
        }


@dataclass
class EvidenceCheckResult:
    """Outcome of one quoted-evidence pass over ≥0 scoring files."""

    version_dir: str
    body_path: str
    scoring_files: List[str] = field(default_factory=list)
    dimensions_checked: int = 0
    findings: List[EvidenceFinding] = field(default_factory=list)

    def passed(self) -> bool:
        """``True`` when zero findings (major or minor) were emitted."""
        return not self.findings

    def to_json(self) -> dict:
        return {
            "check": CHECK_NAME,
            "version_dir": self.version_dir,
            "body_path": self.body_path,
            "scoring_files": self.scoring_files,
            "dimensions_checked": self.dimensions_checked,
            "findings": [f.to_dict() for f in self.findings],
            "pass": self.passed(),
        }


# ---------------------------------------------------------------------------
# Empty-scorecard guard (issue #912)
# ---------------------------------------------------------------------------

# A ``## Dimension scores``-style heading, OR a markdown table header row
# that carries both a "Weight" and a "Score" column. Either signal means
# the text is *meant* to be a scorecard — so if the table parser below
# comes back with zero rows, that is a parse failure, not "no scorecard
# here" (a genuinely scorecard-free text — e.g. plain prose findings —
# never matches either pattern).
_SCORECARD_HEADING_RE = re.compile(
    r"^#+\s*.*\b(?:dimension|scoring)\s+scores?\b", re.IGNORECASE | re.MULTILINE
)
_SCORECARD_HEADER_ROW_RE = re.compile(
    r"^\s*\|.*\bWeight\b.*\|.*\bScore\b.*\|", re.IGNORECASE | re.MULTILINE
)


def _looks_like_scorecard(text: str) -> bool:
    """True when ``text`` carries a scorecard heading or header row.

    Used to distinguish "there is no scorecard in this text" (a clean
    pass with zero dimensions checked) from "there IS a scorecard but it
    failed to parse" (the vacuous-pass bug, issue #912) — only the
    latter must surface as a finding.
    """
    return bool(
        _SCORECARD_HEADING_RE.search(text) or _SCORECARD_HEADER_ROW_RE.search(text)
    )


def _empty_scorecard_finding(scoring_path: str) -> EvidenceFinding:
    """Build the finding for a scorecard-shaped text that parsed to zero rows.

    This is the load-bearing fix for issue #912: previously a fully
    bolded (or otherwise malformed) scoring table parsed to ``[]`` and
    every downstream check trivially "passed" against an empty list —
    the scorecard-arithmetic gate reported clean results despite never
    having checked anything. Emitting a major finding here means the
    gate can no longer report success on an empty scorecard.
    """
    return EvidenceFinding(
        code=EMPTY_SCORECARD,
        severity=SEVERITY_MAJOR,
        dimension="(scorecard)",
        scoring_path=scoring_path,
        score=None,
        weight=0,
        spans_extracted=0,
        message=(
            f"{scoring_path} carries a scorecard heading or a Weight/Score "
            f"header row, but the scoring table parsed to ZERO rows — this "
            f"is treated as a parse failure, not a clean pass. A common "
            f"cause is markdown emphasis (e.g. `**5**`) around a Weight or "
            f"Score cell breaking the row shape; verify the table renders "
            f"as the documented `| # | Dimension | Weight | Score | "
            f"Justification |` shape and re-run this check."
        ),
    )


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------


def classify_justification(
    *,
    dimension: str,
    score: Optional[int],
    weight: int,
    justification: Optional[str],
    normalized_body: str,
    scoring_path: str = "scoring.md",
) -> Optional[EvidenceFinding]:
    """Classify one scoring row. Returns a finding or ``None`` (pass).

    A ``None`` score (the critic does not own the dim) is always a
    pass — the partial-scorecard rule in ``snippets/critics.md``.
    The classification order is documented in the module docstring and
    is load-bearing: a non-matching calibration-suffix quote alongside
    one matching body quote passes via rule 1.
    """
    if score is None:
        return None
    text = justification or ""
    spans = extract_quoted_spans(text)
    # Rule 1: any matching span → pass.
    if any(span_matches_body(s, normalized_body) for s in spans):
        return None
    # Rule 2: ceiling-by-absence → pass.
    if score == weight and has_absence_marker(text):
        return None
    # Rule 3: spans present but none matches the body → major.
    if spans:
        sample = normalize(spans[0])
        if len(sample) > 60:
            sample = sample[:57] + "..."
        return EvidenceFinding(
            code=FABRICATED_EVIDENCE,
            severity=SEVERITY_MAJOR,
            dimension=dimension,
            scoring_path=scoring_path,
            score=score,
            weight=weight,
            spans_extracted=len(spans),
            message=(
                f"dim {dimension!r} (score {score}/{weight}): justification "
                f"quotes {len(spans)} span(s) but NONE appears verbatim in "
                f"the reviewed body — fabricated evidence. First span: "
                f'"{sample}". Re-derive the justification from the actual '
                f"body text."
            ),
        )
    # Rule 4: no spans at all → minor advisory.
    return EvidenceFinding(
        code=MISSING_EVIDENCE,
        severity=SEVERITY_MINOR,
        dimension=dimension,
        scoring_path=scoring_path,
        score=score,
        weight=weight,
        spans_extracted=0,
        message=(
            f"dim {dimension!r} (score {score}/{weight}): justification "
            f"contains no quoted span (≥{MIN_QUOTE_CHARS} chars) from the "
            f"reviewed body"
            + (
                " and no ceiling by-absence marker"
                if score == weight
                else ""
            )
            + ' — add a verbatim quote with a location anchor, e.g. '
            f'("the quoted span" — §2.1)'
            + (
                f", or the marker phrase 'no instance of <X> found' "
                f"(allowed at full weight)."
                if score == weight
                else "."
            )
        ),
    )


def check_scoring_text(
    scoring_text: str,
    body_text: str,
    *,
    scoring_path: str = "scoring.md",
) -> Tuple[List[EvidenceFinding], int]:
    """Run the quoted-evidence check over one scoring.md's text.

    Pure function of the two texts (no filesystem). Returns
    ``(findings, dimensions_checked)`` where ``dimensions_checked``
    counts the non-null-score rows examined. A text that carries a
    scorecard heading or Weight/Score header row but parses to zero
    rows raises an :data:`EMPTY_SCORECARD` finding rather than silently
    returning ``([], 0)`` (issue #912).
    """
    normalized_body = normalize(body_text)
    findings: List[EvidenceFinding] = []
    rows = parse_memo_scoring_table(scoring_text)
    if not rows and _looks_like_scorecard(scoring_text):
        findings.append(_empty_scorecard_finding(scoring_path))
        return findings, 0
    checked = 0
    for row in rows:
        if row.score is None:
            continue
        checked += 1
        finding = classify_justification(
            dimension=row.dimension,
            score=row.score,
            weight=row.max,
            justification=row.justification,
            normalized_body=normalized_body,
            scoring_path=scoring_path,
        )
        if finding is not None:
            findings.append(finding)
    return findings, checked


# ---------------------------------------------------------------------------
# Machine-summary JSON scorecard parsing (issue #496)
# ---------------------------------------------------------------------------


@dataclass
class SummaryDimension:
    """One parsed dimension from a ``_summary.md`` JSON ``dimensions`` block.

    Mirrors the fields :func:`classify_justification` consumes from a
    table ``Score`` row: a ``dimension`` key, a ``score`` (``None`` for
    un-owned dims), a ``weight``, and the ``justification`` string.
    """

    dimension: str
    score: Optional[int]
    weight: int
    justification: Optional[str]


# Matches a fenced ```json ... ``` block. Non-greedy body; the inner
# ``dimensions`` object the ip reviewers emit lives inside the FIRST
# such block (the rubric block + dimensions block + critical_flag are
# all one JSON object). A `_summary.md` may carry prose + a fenced json
# block; we scan every fenced json block and take the first that parses
# to an object carrying a ``dimensions`` mapping.
_JSON_FENCE_RE = re.compile(
    r"```json\s*\n(?P<body>.*?)\n```",
    re.DOTALL | re.IGNORECASE,
)


def _coerce_score(raw: object) -> Optional[int]:
    """Coerce a parsed JSON score value to ``Optional[int]``.

    ``null`` → ``None``; an int passes through; a float that is integral
    (``4.0``) is narrowed; anything else (string ``"n/a"``, a non-
    integral float) is treated as un-owned (``None``) — a defensive
    read, never a crash.
    """
    if raw is None:
        return None
    if isinstance(raw, bool):  # bool is an int subclass — exclude it
        return None
    if isinstance(raw, int):
        return raw
    if isinstance(raw, float) and raw.is_integer():
        return int(raw)
    return None


def parse_machine_summary_dimensions(
    summary_text: str,
) -> List[SummaryDimension]:
    """Parse an OPTIONAL JSON ``dimensions`` block from a ``_summary.md``.

    NOTE (issue #536): this JSON shape is forward-compat / legacy — no
    shipped ip command doc or worked example emits it. The ip skills
    (``ip-uspto``, ``ip-uspto-provisional``) actually write the
    machine-summary scorecard as a markdown TABLE (the same
    ``| # | Dimension | Weight | Score | Justification |`` shape the
    human-verdict path uses; ``critics.py`` and
    ``snippets/scorecard_kind.md`` are the contract). When a ``_summary.md``
    instead carries a fenced ```json``` block with a ``dimensions``
    object — each key a rubric dimension mapping to ``null`` (un-owned)
    or an object with ``score`` + ``justification`` (+ optional
    ``weight``) — this parser reads it; otherwise it returns an empty
    list and :func:`check_summary_text` falls back to the table parser.
    This parser:

    - extracts every fenced ```json``` block and uses the first one
      that parses to an object carrying a ``dimensions`` mapping
      (tolerating a sibling ``rubric`` / ``critical_flag`` key — only
      ``dimensions`` is read);
    - emits one :class:`SummaryDimension` per dimension entry,
      ``json.loads``-coercing the ``score`` and reading ``justification``
      (a missing/``null`` justification becomes ``None``);
    - reads the per-dim ``weight`` when present (provisional D9 is ``/6``;
      most dims are ``/5``); when absent, defaults the weight to the
      dim's own score so a full-score by-absence justification still
      clears rule 2 — un-stamped weight never blocks the
      ceiling-by-absence pass.

    A ``null`` dimension value (un-owned dim) emits a row with
    ``score=None`` (skipped by the caller, parallel to the table path's
    ``null``-score rows). Malformed / absent JSON, or a block without a
    ``dimensions`` mapping, returns an empty list — never raises.
    """
    rows: List[SummaryDimension] = []
    for match in _JSON_FENCE_RE.finditer(summary_text):
        try:
            payload = json.loads(match.group("body"))
        except (ValueError, json.JSONDecodeError):
            continue
        if not isinstance(payload, dict):
            continue
        dims = payload.get("dimensions")
        if not isinstance(dims, dict):
            continue
        for name, entry in dims.items():
            if entry is None:
                rows.append(
                    SummaryDimension(
                        dimension=str(name),
                        score=None,
                        weight=0,
                        justification=None,
                    )
                )
                continue
            if not isinstance(entry, dict):
                # Tolerate a bare numeric value (``"6": 4``) — score with
                # no justification, classified as missing_evidence.
                score = _coerce_score(entry)
                rows.append(
                    SummaryDimension(
                        dimension=str(name),
                        score=score,
                        weight=score if score is not None else 0,
                        justification=None,
                    )
                )
                continue
            score = _coerce_score(entry.get("score"))
            weight_raw = _coerce_score(entry.get("weight"))
            # Un-stamped weight defaults to the score so a full-weight
            # by-absence justification still clears rule 2.
            weight = weight_raw if weight_raw is not None else (
                score if score is not None else 0
            )
            justification = entry.get("justification")
            if justification is not None and not isinstance(
                justification, str
            ):
                justification = str(justification)
            rows.append(
                SummaryDimension(
                    dimension=str(name),
                    score=score,
                    weight=weight,
                    justification=justification,
                )
            )
        return rows  # first dimensions-carrying block wins
    return rows


def check_summary_text(
    summary_text: str,
    body_text: str,
    *,
    scoring_path: str = "_summary.md",
) -> Tuple[List[EvidenceFinding], int]:
    """Run the quoted-evidence check over one ``_summary.md``'s text.

    The machine-summary analog of :func:`check_scoring_text`. The
    canonical machine-summary scorecard is a **markdown table** (the
    ``| # | Dimension | Weight | Score | Justification |`` shape the ip
    commands instruct and the ip examples carry — see
    ``anvil/lib/snippets/scorecard_kind.md`` and ``critics.py``). This
    routine therefore tries two scorecard shapes, in order:

    1. A fenced ```json``` ``dimensions`` block (issue #496), parsed by
       :func:`parse_machine_summary_dimensions`. Forward-compat / legacy:
       no shipped command doc or example actually emits this shape.
    2. When the JSON path yields no checkable rows, **fall back** to the
       same table parser the human-verdict path uses
       (:func:`parse_memo_scoring_table`) over the same text — this is the
       shape the ip ``_summary.md`` scorecards actually carry, so the
       write-time self-check is non-vacuous in real reviews (issue #536).

    Either way, each non-null-score dimension feeds the SAME
    :func:`classify_justification` flow (the classifier, normalization,
    span+elision matching, and the by-absence marker are
    scorecard-source-agnostic). Pure function of the two texts (no
    filesystem). Returns ``(findings, dimensions_checked)``. A text that
    carries a scorecard heading or Weight/Score header row but yields
    zero rows from BOTH the JSON and table parsers raises an
    :data:`EMPTY_SCORECARD` finding rather than silently returning
    ``([], 0)`` (issue #912).
    """
    normalized_body = normalize(body_text)
    findings: List[EvidenceFinding] = []
    checked = 0
    json_rows = parse_machine_summary_dimensions(summary_text)
    for row in json_rows:
        if row.score is None:
            continue
        checked += 1
        finding = classify_justification(
            dimension=row.dimension,
            score=row.score,
            weight=row.weight,
            justification=row.justification,
            normalized_body=normalized_body,
            scoring_path=scoring_path,
        )
        if finding is not None:
            findings.append(finding)
    if checked == 0 and not findings:
        # No JSON-block dimensions parsed (the table-shaped machine-summary
        # scorecard the commands/examples/snippet actually emit — issue
        # #536). Re-run over the markdown table so the self-check is live.
        table_rows = parse_memo_scoring_table(summary_text)
        if (
            not json_rows
            and not table_rows
            and _looks_like_scorecard(summary_text)
        ):
            findings.append(_empty_scorecard_finding(scoring_path))
            return findings, 0
        for trow in table_rows:
            if trow.score is None:
                continue
            checked += 1
            finding = classify_justification(
                dimension=trow.dimension,
                score=trow.score,
                weight=trow.max,
                justification=trow.justification,
                normalized_body=normalized_body,
                scoring_path=scoring_path,
            )
            if finding is not None:
                findings.append(finding)
    return findings, checked


# ---------------------------------------------------------------------------
# Filesystem entry points
# ---------------------------------------------------------------------------


FIXED_BODY_NAMES: Tuple[str, ...] = (
    "main.tex",       # paper
    "report.md",      # report
    "deck.md",        # deck, slides
    "proposal.tex",   # proposal
    "installation.tex",  # installation
    "datasheet.tex",  # datasheet
    "spec.tex",       # ip-uspto, ip-uspto-provisional
)
"""Per-skill fixed body filenames checked after the slug-echo shape.

Issue #475 rollout: the verifier resolves the slug-echo ``<slug>.md``
(memo, essay) first, then these fixed names in order. Order is
load-bearing only for the pathological version dir carrying two body
files — first hit wins.
"""


MACHINE_SUMMARY_KIND = "machine-summary"
"""``_meta.json`` ``scorecard_kind`` value routing to the summary parser."""

_SUMMARY_FILENAME = "_summary.md"
_SCORING_FILENAME = "scoring.md"


def scorecard_kind_for(scoring_file: Path) -> Optional[str]:
    """Read the ``scorecard_kind`` discriminator for a critic-sibling file.

    Reads the sibling ``_meta.json`` next to ``scoring_file`` and returns
    its ``scorecard_kind`` field (the discriminator contract in
    ``anvil/lib/snippets/scorecard_kind.md``). Returns ``None`` when no
    ``_meta.json`` exists or it lacks the field / is malformed — the
    caller then falls back to filename-shape routing (a ``_summary.md``
    is machine-summary; a ``scoring.md`` is the table path). Never
    raises.
    """
    meta = scoring_file.parent / "_meta.json"
    if not meta.is_file():
        return None
    try:
        payload = json.loads(meta.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    if not isinstance(payload, dict):
        return None
    kind = payload.get("scorecard_kind")
    return kind if isinstance(kind, str) else None


def _is_machine_summary(scoring_file: Path) -> bool:
    """``True`` when ``scoring_file`` should route to the summary parser.

    Dispatch is by the sibling ``_meta.json`` ``scorecard_kind`` when it
    is present and authoritative (issue #496 — NOT a hardcoded skill
    name); otherwise it falls back to the filename shape (a
    ``_summary.md`` is machine-summary, a ``scoring.md`` is the table).
    The meta discriminator wins when present so a future machine-summary
    skill that names its scorecard differently still routes correctly.
    """
    kind = scorecard_kind_for(scoring_file)
    if kind is not None:
        return kind == MACHINE_SUMMARY_KIND
    return scoring_file.name == _SUMMARY_FILENAME


def discover_scoring_files(version_dir: Path) -> List[Path]:
    """Discover critic-sibling scorecard files for a version dir.

    Matches ``<version_dir>.<critic>/scoring.md`` (the ``human-verdict``
    table shape) AND ``<version_dir>.<critic>/_summary.md`` (the
    ``machine-summary`` JSON shape — issue #496) siblings, sorted by
    path. When a sibling carries BOTH files (an aggregator critic per
    ``snippets/scorecard_kind.md``), only the one matching its
    ``_meta.json`` ``scorecard_kind`` is checked — the other shape is
    the secondary deliverable, not the scorecard of record.
    Leading-dot staging dirs (``.<name>.tmp/``) never match the glob.
    """
    version_dir = Path(version_dir)
    table = version_dir.parent.glob(f"{version_dir.name}.*/{_SCORING_FILENAME}")
    summary = version_dir.parent.glob(
        f"{version_dir.name}.*/{_SUMMARY_FILENAME}"
    )
    chosen: List[Path] = []
    for path in sorted([*table, *summary]):
        kind = scorecard_kind_for(path)
        if kind == MACHINE_SUMMARY_KIND and path.name != _SUMMARY_FILENAME:
            continue  # machine-summary critic: skip its table file
        if (
            kind is not None
            and kind != MACHINE_SUMMARY_KIND
            and path.name == _SUMMARY_FILENAME
        ):
            continue  # human-verdict critic: skip its summary file
        chosen.append(path)
    return chosen


def check_version_dir(
    version_dir: Path,
    *,
    scoring: Optional[Path] = None,
    body: Optional[Path] = None,
) -> EvidenceCheckResult:
    """Run the check for a version directory.

    Without ``scoring``, discovers every critic-sibling ``scoring.md``
    via :func:`discover_scoring_files` (zero siblings is a clean pass —
    advisory posture over legacy dirs). With ``scoring``, checks
    exactly that one file (the reviewer's staging-dir self-check path).

    ``body`` overrides body-file discovery (for adopted-in-place legacy
    threads whose entry point isn't ``<slug>.md``/:data:`FIXED_BODY_NAMES`,
    e.g. a ``paper.tex``); when omitted, behavior is byte-identical to
    the historical discovery chain.

    Raises ``FileNotFoundError`` when the version dir, its body file (or
    a missing ``--body`` override), or an explicitly-passed ``scoring``
    file is missing.
    """
    version_dir = Path(version_dir).resolve()
    if not version_dir.is_dir():
        raise FileNotFoundError(
            f"evidence_check: version_dir {version_dir!s} does not exist "
            f"or is not a directory."
        )
    body_file = resolve_body_path(
        version_dir,
        body=body,
        fallback_names=FIXED_BODY_NAMES,
        caller_name="evidence_check",
    )
    body_text = body_file.read_text(encoding="utf-8")

    # Multi-file LaTeX threads (issue #643): a paper ``main.tex`` that
    # ``\input``/``\include``s section files has its real content in the
    # children. Without this expansion a reviewer who (correctly, per
    # paper-review.md step 4) reads the full resolved body and quotes a
    # child section would trip a false ``fabricated_evidence`` finding —
    # the quote is verbatim from ``sections/intro.tex`` but absent from the
    # ~90-line ``main.tex`` shell. Expand ``.tex`` bodies to the resolved
    # tree so quote-verification checks against the same document the
    # reviewer scored. Non-``.tex`` bodies (markdown skills) are unchanged.
    if body_file.suffix == ".tex":
        from anvil.lib.tex_includes import resolve_tex_inputs

        resolved = resolve_tex_inputs(body_file)
        if len(resolved.files) > 1:
            body_text = resolved.body

    if scoring is not None:
        scoring = Path(scoring)
        if not scoring.is_file():
            raise FileNotFoundError(
                f"evidence_check: --scoring file {scoring!s} does not exist."
            )
        scoring_files = [scoring]
    else:
        scoring_files = discover_scoring_files(version_dir)

    result = EvidenceCheckResult(
        version_dir=version_dir.name,
        body_path=record_body_path(version_dir, body_file),
        scoring_files=[str(p) for p in scoring_files],
    )
    for path in scoring_files:
        checker = (
            check_summary_text
            if _is_machine_summary(path)
            else check_scoring_text
        )
        findings, checked = checker(
            path.read_text(encoding="utf-8"),
            body_text,
            scoring_path=str(path),
        )
        result.findings.extend(findings)
        result.dimensions_checked += checked
    return result


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.evidence_check",
        description=(
            "Quoted-evidence verifier for critic scoring tables: checks "
            "that each scoring.md justification embeds at least one "
            "verbatim quote from the reviewed body (or the 'no instance "
            "of <X> found' by-absence marker at full weight). Advisory — "
            "reports findings, never mutates, never writes a sidecar."
        ),
    )
    p.add_argument(
        "version_dir",
        help=(
            "Path to <thread>.{N}/ containing the body file: <slug>.md "
            "(slug-echo) or one of main.tex, report.md, deck.md, "
            "proposal.tex, installation.tex, datasheet.tex, spec.tex."
        ),
    )
    p.add_argument(
        "--scoring",
        metavar="PATH",
        default=None,
        help=(
            "Check exactly this scoring.md (table) or _summary.md "
            "(machine-summary JSON dimensions block) instead of "
            "discovering critic-sibling files (the reviewer's "
            "staging-dir self-check path). Routing is by filename shape "
            "and the sibling _meta.json scorecard_kind."
        ),
    )
    p.add_argument(
        "--body",
        metavar="PATH",
        default=None,
        help=(
            "Override body-file discovery (e.g. for adopted-in-place "
            "legacy threads whose entry point isn't <slug>.md or one of "
            "the FIXED_BODY_NAMES, such as a paper.tex). Relative paths "
            "resolve against version_dir; absolute paths are used as-is. "
            "The resolved (portfolio-relative) path is recorded in the "
            "printed JSON's body_path."
        ),
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Returns the process exit code.

    Exit codes:
    - ``0``: clean pass (zero findings — including zero scoring files).
    - ``1``: one or more findings (major fabricated-evidence or minor
      missing-evidence).
    - ``2``: invocation error (missing version_dir, body file, or
      ``--scoring`` file).
    """
    parser = _build_cli_parser()
    args = parser.parse_args(argv)
    try:
        result = check_version_dir(
            Path(args.version_dir),
            scoring=Path(args.scoring) if args.scoring else None,
            body=Path(args.body) if args.body else None,
        )
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result.to_json(), indent=2))
    return 0 if result.passed() else 1


__all__ = [
    "CHECK_NAME",
    "MIN_QUOTE_CHARS",
    "ELISION_WINDOW_CHARS",
    "FABRICATED_EVIDENCE",
    "FIXED_BODY_NAMES",
    "MISSING_EVIDENCE",
    "EMPTY_SCORECARD",
    "SEVERITY_MAJOR",
    "SEVERITY_MINOR",
    "EvidenceFinding",
    "EvidenceCheckResult",
    "normalize",
    "extract_quoted_spans",
    "has_absence_marker",
    "span_matches_body",
    "classify_justification",
    "check_scoring_text",
    "check_summary_text",
    "parse_machine_summary_dimensions",
    "SummaryDimension",
    "MACHINE_SUMMARY_KIND",
    "scorecard_kind_for",
    "discover_scoring_files",
    "check_version_dir",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
