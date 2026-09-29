"""Deterministic numeric-consistency gate (issue #462).

Fourth member of the deterministic-checks family (alongside
``anvil/lib/render_gate.py``, ``anvil/lib/marp_lint.py``,
``anvil/lib/revise_consistency.py``, and ``anvil/lib/scorecard_check.py``).
It catches the **claim-vs-claim** numeric failure mode bred at the
rjwalters.info consumer (the "spread failure"): a body paragraph names
the raw values 70 / 56 / 54, then asserts a "70-point spread" (the raw
top score leaked into the spread slot) and "16 points ahead" (the named
gap is 14). Note the axis distinction from the refs-vs-claim checks
(datasheet internal-consistency dim, report data-contract audit #428):
this module validates numbers **within the body against each other**,
not against external evidence files.

Deterministic subset (pure regex/arithmetic — no LLM, no new deps)
-------------------------------------------------------------------

1. **Number extraction** — digits with common affixes: ``$2.3B``
   (currency with K/M/B scale), ``42%`` (percent), ``8x`` (multiplier),
   ``70-point`` / ``12 ms`` / bare integers (counts). Spelled-out
   numbers ("sixteen") are OUT of v1 — false-positive discipline per
   the ``citation_coverage.py`` conservative-detector contract.
   Numbers inside code fences, inline code spans, URLs, markdown link
   targets, pandoc citation keys (``@smith2024``), LaTeX
   ``\\cite/\\ref/\\label`` arguments, and LaTeX comments are masked out
   before extraction. Four-digit numbers in 1900–2100 are treated as
   years and excluded from candidate pools. Markdown ordered-list
   markers (``1.`` at line start) are excluded.

2. **Arithmetic-claim patterns** — each claim is validated against
   candidate values in a same-paragraph (±1 paragraph) window:

   - ``N-point spread/gap`` (population claims): valid iff
     ``max(candidates) − min(candidates) ≈ N``. The spread of a
     population IS max − min.
   - ``N-point lead/margin`` / ``N points ahead/behind/clear``
     (ranked-leader claims): valid iff
     ``max(candidates) − second_max(candidates) ≈ N``. Deterministic
     heuristic: "ahead"/"lead" claims overwhelmingly describe the
     leader vs the runner-up. A claim about second-vs-third place can
     false-positive — this module is warn-only and suppressible
     (see Suppression below), which is the documented FP budget.
   - ``X% of`` (proportion claims): validated ONLY when the window
     contains an explicit fraction shape (``a of b``, ``a out of b``,
     ``a/b``); valid iff some fraction computes ``a/b ≈ X%`` (a
     window-wide numeric match always silences the finding — matching
     pairs are preferred over mismatching ones, regardless of subject).
     Absent a numeric match, a mismatch is only reported against a
     fraction that shares a **lexical anchor** with the claim — a
     content word (subject noun, function words dropped) present in
     both the claim's sentence and the fraction's sentence (issue
     #854: "27.3% of readable cells" must not pair with an unrelated
     "18/18 pages" fraction just because it is the nearest fraction in
     the paragraph — they describe different subjects). No fraction
     shape in the window, or no anchor-sharing fraction once a numeric
     match has been ruled out → silent skip (conservative).
   - ``X% more/less/higher/lower/faster/slower/...`` (relative-change
     claims): validated ONLY when the window contains an explicit pair
     shape (``from A to B``, ``A vs B``, ``A → B``); valid iff some
     pair computes a relative change ≈ X% under either direction
     convention. No pair shape → silent skip.
   - ``Nx speedup/faster/...`` (multiplier claims): same pair-shape
     gating; valid iff some pair ratio ``a/b ≈ N`` (either order).

   Candidate pools are **class-segregated**: percent tokens never feed
   point-difference claims, counts never feed percent claims directly
   (only via explicit fraction/pair shapes) — percentages vs absolute
   counts in the same window never cross-match.

3. **Unbridged-population flag** (the spread failure): a spread/gap or
   lead claim whose value computes from NO window pair while the window
   names ≥2 candidates AND the claim value coincides with a raw window
   value. This is the exact canary shape: "70-point spread" where 70 is
   the top raw score, not any difference.

4. **Tolerance policy** (the rounding contract): a claim passes when
   the claimed value is within **±1 unit** of the computed value OR
   within **±5% relative** of it, whichever is more permissive. For
   percent claims the unit is one percentage point. Examples: a "50%"
   claim over 47/94 (= 50.0%) passes exactly; a "15-point lead" over
   70/56 (= 14) passes via ±1; a "17-point lead" over the same values
   fails (off by 3, > 1 unit and > 5%). The "same quantity stated twice
   disagrees" check (8x here, 10x there) did NOT clear the FP bar with
   a conservative keyword heuristic and is left to the LLM review step
   per the issue #462 curation.

Severity wiring (advisory v1; ``blocking=True`` for essay #460)
----------------------------------------------------------------

Findings emit at warning severity (schema ``Finding.severity="minor"``)
with NO ``CriticalFlag`` — the ``memo_image_dimensions`` /
``revise_consistency`` warn-only model. ``to_review(blocking=True)``
additionally emits one ``CriticalFlag`` per finding-code cluster, which
forces ``Verdict.BLOCK`` through ``critics.compute_verdict``. The essay
skill (#460) is the shipped ``blocking=True`` consumer: ``essay-review``
invokes the CLI with ``--blocking`` as its convergence-blocking
numeric gate (memo/paper stay advisory).

Suppression
-----------

``<!-- anvil-lint-disable: numeric_consistency -->`` on the claim's
line or the line immediately above downgrades that claim's findings to
severity ``"info"`` (schema ``"nit"``) — recorded but never gating,
mirroring the memo lint-disable convention (``memo_image_refs_exist``,
``memo_deck_parity``). Suppressed findings never produce critical
flags, even under ``blocking=True``, and do not affect ``passed()``.

Sidecar + discovery contract
----------------------------

``write_review_dir`` writes ``<thread>.{N}.numeric/_review.json`` via
``anvil/lib/sidecar.py::staged_sidecar`` (crash-safe atomic rename).
The ``.numeric`` tag is a single segment, so
``critics.discover_critics`` picks the sidecar up with **no aggregator
change** — same coordination shape as ``.hyperlinks/`` (#335) and
``.citations/`` (#336).

Link audit / example coherence (issue #462 scope record)
--------------------------------------------------------

The citation/link-audit gate is NOT built here by design: the
link-resolution half already ships as
``anvil/skills/memo/lib/hyperlink_resolver.py`` (#335) and
``anvil/skills/memo/lib/citation_coverage.py`` (#336); the essay skill
(#460) is the awaited second consumer that promotes
``hyperlink_resolver`` (and assesses ``citation_coverage``) from the
memo skill-local lib to ``anvil/lib/``. The example-coherence gate is
deferred (irreducibly an LLM pass with one observed production
failure); #460's review command carries the prose check directly.

CLI entry-point
---------------

``python -m anvil.lib.numeric_consistency <version_dir>
[--write-review] [--blocking] [--body PATH]``

Writes a JSON summary to stdout. Exit codes: ``0`` clean (or
suppressed-only findings), ``1`` active findings, ``2`` invocation
error. The body file is auto-detected: ``<slug>.md`` (the #295
slug-echo memo shape) first, then ``main.tex`` (the paper shape).
``--body PATH`` overrides discovery for adopted-in-place legacy
threads whose entry point isn't ``<slug>.md``/``main.tex`` (e.g. a
``paper.tex``); with ``--write-review`` the resolved
portfolio-relative path is what the ``.numeric/_review.json`` sidecar
records.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Tuple

from anvil.lib.body_resolution import record_body_path, resolve_body_path
from anvil.lib.review_schema import (
    CriticalFlag,
    Finding,
    Kind,
    Review,
    Score,
)
from anvil.lib.sidecar import write_critic_review_dir


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CRITIC_ID = "numeric"
"""Stable identifier for this critic in ``_review.json.critic_id``."""

CHECK_NAME = "numeric_consistency"
"""Check identifier echoed in JSON payloads and the suppression rule."""

DIM_NUMERIC = "numeric_consistency"
"""Dimension name surfaced on every emitted Finding."""

NUMERIC_SUFFIX = "numeric"
"""Sidecar dir tag: ``<thread>.{N}.numeric/``. Single segment so
``critics.discover_critics`` picks it up with no aggregator change."""

CRITICAL_NUMERIC_INCONSISTENCY = "critical_numeric_inconsistency"
"""Critical-flag ``type`` prefix emitted ONLY under ``blocking=True``
(the essay #460 convergence-blocking hook). The full type is
``critical_numeric_inconsistency:<finding-code>`` — one flag per
finding-code cluster."""

# Finding codes (stable identifiers; consumers grep for these).
GAP_MISMATCH = "gap_mismatch"
UNBRIDGED_POPULATION = "unbridged_population"
PERCENT_MISMATCH = "percent_mismatch"
MULTIPLIER_MISMATCH = "multiplier_mismatch"

# Internal severities. "warning" findings are the advisory surface;
# "info" findings are suppressed hits (recorded, never gating).
SEVERITY_WARNING = "warning"
SEVERITY_INFO = "info"

# Tolerance policy (documented in the module docstring): a claim passes
# when |claimed - computed| <= ABS_TOLERANCE or the relative error
# |claimed - computed| / |computed| <= REL_TOLERANCE.
ABS_TOLERANCE = 1.0
REL_TOLERANCE = 0.05

# Year heuristic: bare 4-digit integers in this range are calendar years,
# not quantities — excluded from candidate pools.
_YEAR_MIN, _YEAR_MAX = 1900, 2100

# Suppression directive (shared shape with render_gate / parity).
_LINT_DISABLE_RE = re.compile(
    r"<!--\s*anvil-lint-disable:\s*(?P<rules>[a-zA-Z0-9_,\-\s]+?)\s*-->",
)


# ---------------------------------------------------------------------------
# Masking (code fences, inline code, URLs, citation keys, LaTeX args)
# ---------------------------------------------------------------------------

_COMMON_MASK_PATTERNS: Tuple[re.Pattern, ...] = (
    # Fenced code blocks (``` ... ``` or ~~~ ... ~~~), multi-line.
    re.compile(r"(```|~~~).*?\1", re.DOTALL),
    # Inline code spans.
    re.compile(r"`[^`\n]*`"),
    # URLs (bare or inside link targets).
    re.compile(r"(?:https?|ftp)://[^\s)\]>]+"),
    # Markdown link targets: the (...) following [text].
    re.compile(r"(?<=\])\([^)\s]*\)"),
    # Pandoc citation keys: @smith2024 (with optional surrounding [-@]).
    re.compile(r"@[A-Za-z][A-Za-z0-9_:.\-]*"),
    # LaTeX \cite/\ref/\label/\eqref/\pageref/\bibitem arguments.
    re.compile(r"\\(?:cite\w*|ref|eqref|pageref|label|bibitem)\s*(?:\[[^\]]*\])?\{[^}]*\}"),
)

# LaTeX-only: unescaped % starts a comment. MUST NOT run on markdown,
# where a bare "50%" is a percent token, not a comment opener.
_LATEX_COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")


def _mask_text(text: str, *, latex: bool = False) -> str:
    """Blank out non-prose regions while preserving offsets/line numbers.

    Every masked character is replaced with a space (newlines inside
    masked regions are preserved) so token positions and line numbers in
    the masked text map 1:1 to the original. The LaTeX comment rule is
    flavor-gated: it only applies when ``latex=True`` (a ``main.tex``
    body), because a bare ``%`` in markdown is a percent sign.
    """

    def blank(m: re.Match) -> str:
        return "".join(c if c == "\n" else " " for c in m.group(0))

    masked = text
    for pattern in _COMMON_MASK_PATTERNS:
        masked = pattern.sub(blank, masked)
    if latex:
        masked = _LATEX_COMMENT_RE.sub(blank, masked)
    return masked


# ---------------------------------------------------------------------------
# Paragraph segmentation
# ---------------------------------------------------------------------------


def _paragraph_index(text: str) -> List[Tuple[int, int, int]]:
    """Return ``[(start_offset, end_offset, paragraph_idx), ...]``.

    Paragraphs are runs of non-blank lines separated by one or more
    blank lines. Operates on the ORIGINAL text so offsets are shared
    with the masked text (masking preserves offsets).
    """
    spans: List[Tuple[int, int, int]] = []
    idx = 0
    start: Optional[int] = None
    offset = 0
    for line in text.splitlines(keepends=True):
        if line.strip():
            if start is None:
                start = offset
        else:
            if start is not None:
                spans.append((start, offset, idx))
                idx += 1
                start = None
        offset += len(line)
    if start is not None:
        spans.append((start, offset, idx))
    return spans


def _paragraph_of(offset: int, spans: List[Tuple[int, int, int]]) -> int:
    """Return the paragraph index containing ``offset`` (nearest if in a gap)."""
    for s, e, i in spans:
        if s <= offset < e:
            return i
    # Offset in an inter-paragraph gap (or EOF): attribute to the last
    # paragraph that started before it.
    best = 0
    for s, _e, i in spans:
        if s <= offset:
            best = i
    return best


def _line_of(offset: int, text: str) -> int:
    """1-based line number of ``offset`` in ``text``."""
    return text.count("\n", 0, offset) + 1


# ---------------------------------------------------------------------------
# Lexical-anchor gating (issue #854)
# ---------------------------------------------------------------------------

# Closed-class function words dropped from anchor tokens. Domain nouns
# ("cells", "pages", "respondents", ...) are never filtered — only
# generic connective/grammatical words too common to signal a shared
# subject between a percent claim and a candidate fraction.
_ANCHOR_STOPWORDS = frozenset({
    "the", "a", "an", "of", "in", "on", "at", "to", "for", "with", "and",
    "or", "is", "are", "was", "were", "this", "that", "these", "those",
    "it", "its", "as", "by", "from", "we", "our", "be", "been", "being",
    "than", "over", "under", "into", "out", "about", "which", "who",
    "whom", "have", "has", "had", "will", "would", "can", "could",
    "not", "but", "so", "if", "then", "also", "very", "some", "all",
    "each", "any", "more", "most", "other", "such", "no", "only",
    "same", "just", "per", "there", "here", "now", "when", "where",
})

_ANCHOR_WORD_RE = re.compile(r"[A-Za-z][A-Za-z\-]*")
# Sentence terminator: '.', '!', or '?' followed by whitespace/EOF. Bounds
# anchor windows to the enclosing sentence so a claim and an unrelated
# fraction one sentence later never bleed tokens into each other's
# window (the census-reader false positive this gate closes).
_SENTENCE_END_RE = re.compile(r"[.!?](?=\s|$)")


def _sentence_span(
    masked: str, start: int, end: int, para_start: int, para_end: int
) -> Tuple[int, int]:
    """Bound ``[start, end)`` to its enclosing sentence within the paragraph.

    Falls back to the full paragraph bounds when no sentence-terminating
    punctuation is found on one side (e.g. a table row or heading with
    no period).
    """
    before_region = masked[para_start:start]
    s = para_start
    last_end: Optional[int] = None
    for m in _SENTENCE_END_RE.finditer(before_region):
        last_end = m.end()
    if last_end is not None:
        s = para_start + last_end
    after_region = masked[end:para_end]
    m2 = _SENTENCE_END_RE.search(after_region)
    e = para_end if m2 is None else end + m2.end()
    return s, e


def _anchor_tokens(
    masked: str,
    start: int,
    end: int,
    para_start: int,
    para_end: int,
    *,
    window_words: int = 6,
) -> frozenset:
    """Content-word anchors near a claim/shape span (issue #854).

    Extracts up to ``window_words`` content words (letters only, length
    >= 3, closed-class function words dropped per ``_ANCHOR_STOPWORDS``)
    immediately before and after ``[start, end)``, bounded to the
    enclosing sentence (see :func:`_sentence_span`). Used to require a
    shared subject between a percent claim and the fraction it is
    validated against, instead of pairing with whatever fraction is
    merely nearest.
    """
    s_start, s_end = _sentence_span(masked, start, end, para_start, para_end)
    before_words = _ANCHOR_WORD_RE.findall(masked[s_start:start])[-window_words:]
    after_words = _ANCHOR_WORD_RE.findall(masked[end:s_end])[:window_words]
    tokens = {w.lower() for w in before_words + after_words}
    return frozenset(t for t in tokens if len(t) >= 3 and t not in _ANCHOR_STOPWORDS)


# ---------------------------------------------------------------------------
# Number / shape extraction
# ---------------------------------------------------------------------------


def _parse_value(raw: str) -> float:
    """Parse a numeric string (commas allowed) into a float."""
    return float(raw.replace(",", ""))


_SCALE = {
    "k": 1e3,
    "m": 1e6,
    "b": 1e9,
    "t": 1e12,
    "mn": 1e6,
    "bn": 1e9,
    "tn": 1e12,
}

# Scale-suffix alternation shared by _CURRENCY_RE, _FRACTION_RES and
# _PAIR_RES. Two-letter financial-journalism suffixes (bn=billion,
# mn=million, tn=trillion) are listed FIRST so the longest match wins
# over the single-letter b/m/t branch — otherwise "$5bn" would tokenize
# as "$5b" and leave a stray "n". The captured suffix is lowercased
# before the _SCALE lookup, so "Bn"/"Mn" casing is handled for free.
# Keep this single source of truth mirrored across all five sites
# (the #488 invariant).
_SCALE_SUFFIX = r"(?:[KkMmBbTt]n|[KMBkmbTt])"

# Currency: $2.3B / $1,200 / $42 / $5bn. Scale suffix optional.
_CURRENCY_RE = re.compile(
    r"\$\s?(?P<num>\d[\d,]*(?:\.\d+)?)\s?(?P<scale>" + _SCALE_SUFFIX + r")?\b"
)
# Percent: 42% / 42.5 % / LaTeX-escaped 42\%.
_PERCENT_RE = re.compile(r"(?P<num>\d[\d,]*(?:\.\d+)?)\s?\\?%")
# Multiplier: 8x / 8.5× (x must not start a longer word).
_MULTIPLIER_RE = re.compile(r"\b(?P<num>\d+(?:\.\d+)?)\s?(?P<x>[x×])(?![A-Za-z])")
# Bare / unit-bearing numbers (counts): 70 / 1,200 / 12.5. Unit word, if
# any, is irrelevant to the value — we capture the number only.
_COUNT_RE = re.compile(r"(?<![\w.])(?P<num>\d[\d,]*(?:\.\d+)?)(?![\w%])")
# Markdown ordered-list marker at line start: "1. " — not a quantity.
_LIST_MARKER_RE = re.compile(r"^\s*\d+\.\s", re.MULTILINE)

# Explicit fraction shapes (proportion-claim evidence): "47 of 94",
# "47 out of 94", "47/94". Currency prefixes carry an optional K/M/B
# scale suffix per operand ("$1.2B of $2.4B"); the suffix group is a
# conditional `(?(c?)...)` so bare-number text keeps its exact pre-#469
# match surface (a bare "m" stays meters/minutes, never millions).
_FRACTION_RES: Tuple[re.Pattern, ...] = (
    re.compile(
        r"(?<![\w.])(?P<ca>\$\s?)?(?P<a>\d[\d,]*(?:\.\d+)?)"
        r"(?(ca)\s?(?P<sa>" + _SCALE_SUFFIX + r")?\b)"
        r"\s+(?:out\s+of|of)\s+(?:the\s+)?"
        r"(?P<cb>\$\s?)?(?P<b>\d[\d,]*(?:\.\d+)?)"
        r"(?(cb)\s?(?P<sb>" + _SCALE_SUFFIX + r")?\b)(?![\w%])"
    ),
    re.compile(r"(?<![\w.])(?P<a>\d[\d,]*)\s*/\s*(?P<b>\d[\d,]*)(?![\w%])"),
)

# The bare slash-fraction pattern above (index 1) also matches
# season/fiscal-year labels like "2018/19" or "2018/2019" — a=2018,
# b=19 is NOT a fraction and must not become _PairShape evidence
# (issue #836: "2018/19 baseline" sharing a paragraph with an
# unrelated "40% of ..." claim produced a bogus 2018/19 = 10621%
# percent_mismatch). Identity-checked against this specific pattern in
# _extract_shapes so the "of"/"out of" pattern (index 0) and
# _PAIR_RES are untouched — genuine fractions like "47 of 94" / "47/94"
# keep working unchanged.
_SLASH_FRACTION_RE = _FRACTION_RES[1]


def _is_season_fiscal_year_label(a_raw: str, b_raw: str) -> bool:
    """True when a slash pair looks like a season/fiscal-year label.

    Two shapes, both anchored on the existing ``_YEAR_MIN``/``_YEAR_MAX``
    calendar-year heuristic (module-level, reused rather than
    duplicated):

    - ``YYYY/YY`` (e.g. ``2018/19``): numerator is a bare 4-digit year,
      denominator is a bare 1-2 digit integer.
    - ``YYYY/YYYY`` (e.g. ``2018/2019``): both operands are bare 4-digit
      years.

    A comma anywhere in either operand (e.g. ``2,018``) disqualifies it
    — ``str.isdigit()`` returns ``False`` for a comma-bearing string, so
    that case falls through to "not a label" for free.
    """

    def _is_year(raw: str) -> bool:
        return len(raw) == 4 and raw.isdigit() and _YEAR_MIN <= int(raw) <= _YEAR_MAX

    if not _is_year(a_raw):
        return False
    if b_raw.isdigit() and len(b_raw) <= 2:
        return True
    return _is_year(b_raw)

# Explicit pair shapes (ratio / relative-change evidence): "from 120 ms
# to 15 ms", "120 vs 15", "120 → 15". Currency prefixes tolerated, and
# (mirroring _CURRENCY_RE) currency-prefixed operands carry an optional
# K/M/B scale suffix ("from $1.2B to $600M"). The suffix slot must come
# BEFORE the unit-word slot ([A-Za-z%]*), which otherwise swallows it;
# it is currency-gated (conditional on the `$` group) so a bare "12 m"
# is never misread as 12 million.
_PAIR_RES: Tuple[re.Pattern, ...] = (
    re.compile(
        r"\bfrom\s+(?P<ca>\$\s?)?(?P<a>\d[\d,]*(?:\.\d+)?)"
        r"(?(ca)\s?(?P<sa>" + _SCALE_SUFFIX + r")?\b)\s*[A-Za-z%]*\s+to\s+"
        r"(?P<cb>\$\s?)?(?P<b>\d[\d,]*(?:\.\d+)?)"
        r"(?(cb)\s?(?P<sb>" + _SCALE_SUFFIX + r")?\b)"
    ),
    re.compile(
        r"(?P<ca>\$\s?)?(?P<a>\d[\d,]*(?:\.\d+)?)"
        r"(?(ca)\s?(?P<sa>" + _SCALE_SUFFIX + r")?\b)\s*[A-Za-z%]*\s+(?:vs\.?|versus)\s+"
        r"(?P<cb>\$\s?)?(?P<b>\d[\d,]*(?:\.\d+)?)"
        r"(?(cb)\s?(?P<sb>" + _SCALE_SUFFIX + r")?\b)"
    ),
    re.compile(
        r"(?P<ca>\$\s?)?(?P<a>\d[\d,]*(?:\.\d+)?)"
        r"(?(ca)\s?(?P<sa>" + _SCALE_SUFFIX + r")?\b)\s*[A-Za-z%]*\s*(?:→|->)\s*"
        r"(?P<cb>\$\s?)?(?P<b>\d[\d,]*(?:\.\d+)?)"
        r"(?(cb)\s?(?P<sb>" + _SCALE_SUFFIX + r")?\b)"
    ),
)


@dataclass(frozen=True)
class NumberToken:
    """One extracted number with its class and position."""

    raw: str
    value: float
    kind: str  # "currency" | "percent" | "multiplier" | "count"
    start: int
    end: int
    line: int
    paragraph: int


def _extract_numbers(masked: str, spans: List[Tuple[int, int, int]]) -> List[NumberToken]:
    """Extract every classed number token from the masked text.

    Class precedence: currency > percent > multiplier > count. A span
    consumed by a higher-precedence class is not re-tokenized by a
    lower one. Year-looking bare integers and ordered-list markers are
    excluded from the count class.
    """
    tokens: List[NumberToken] = []
    consumed: List[Tuple[int, int]] = []

    def overlaps(s: int, e: int) -> bool:
        return any(s < ce and e > cs for cs, ce in consumed)

    list_marker_spans = [(m.start(), m.end()) for m in _LIST_MARKER_RE.finditer(masked)]

    def in_list_marker(s: int, e: int) -> bool:
        return any(s >= ms and e <= me for ms, me in list_marker_spans)

    for kind, pattern in (
        ("currency", _CURRENCY_RE),
        ("percent", _PERCENT_RE),
        ("multiplier", _MULTIPLIER_RE),
        ("count", _COUNT_RE),
    ):
        for m in pattern.finditer(masked):
            s, e = m.start(), m.end()
            if overlaps(s, e):
                continue
            value = _parse_value(m.group("num"))
            if kind == "currency":
                scale = (m.groupdict().get("scale") or "").lower()
                if scale in _SCALE:
                    value *= _SCALE[scale]
            if kind == "count":
                if in_list_marker(s, e):
                    continue
                # Year heuristic: bare 4-digit integers in 1900-2100.
                if value.is_integer() and _YEAR_MIN <= value <= _YEAR_MAX and len(m.group("num")) == 4:
                    continue
            tokens.append(
                NumberToken(
                    raw=m.group(0),
                    value=value,
                    kind=kind,
                    start=s,
                    end=e,
                    line=_line_of(s, masked),
                    paragraph=_paragraph_of(s, spans),
                )
            )
            consumed.append((s, e))
    tokens.sort(key=lambda t: t.start)
    return tokens


@dataclass(frozen=True)
class _PairShape:
    """One explicit ``(a, b)`` shape (fraction or pair) with position."""

    a: float
    b: float
    raw: str
    start: int
    end: int
    paragraph: int
    anchors: frozenset = field(default_factory=frozenset)
    """Nearby content-word tokens (issue #854 lexical-anchor gating).
    Only consumed by proportion-claim validation today; computed for
    every shape uniformly since it's cheap and position-derived."""


def _shape_operand(m: "re.Match[str]", num_key: str, cur_key: str, scale_key: str) -> float:
    """Parse one shape operand, applying K/M/B scale for currency operands.

    Mirrors the _CURRENCY_RE scale handling in _extract_numbers. The
    scale suffix is only honored when the operand is currency-prefixed
    (the `$` group matched) — see the ambiguity note on _PAIR_RES.
    Patterns without currency/scale groups (e.g. the slash fraction)
    fall through to the raw value.
    """
    value = _parse_value(m.group(num_key))
    groups = m.groupdict()
    if groups.get(cur_key):
        scale = (groups.get(scale_key) or "").lower()
        if scale in _SCALE:
            value *= _SCALE[scale]
    return value


def _extract_shapes(
    masked: str, spans: List[Tuple[int, int, int]], patterns: Tuple[re.Pattern, ...]
) -> List[_PairShape]:
    shapes: List[_PairShape] = []
    para_bounds = {i: (s, e) for s, e, i in spans}
    for pattern in patterns:
        for m in pattern.finditer(masked):
            if pattern is _SLASH_FRACTION_RE and _is_season_fiscal_year_label(
                m.group("a"), m.group("b")
            ):
                continue
            try:
                a = _shape_operand(m, "a", "ca", "sa")
                b = _shape_operand(m, "b", "cb", "sb")
            except ValueError:
                continue
            paragraph = _paragraph_of(m.start(), spans)
            p_start, p_end = para_bounds.get(paragraph, (0, len(masked)))
            shapes.append(
                _PairShape(
                    a=a,
                    b=b,
                    raw=m.group(0),
                    start=m.start(),
                    end=m.end(),
                    paragraph=paragraph,
                    anchors=_anchor_tokens(masked, m.start(), m.end(), p_start, p_end),
                )
            )
    return shapes


# ---------------------------------------------------------------------------
# Claim extraction
# ---------------------------------------------------------------------------

# Diff claims. Kind discriminator: "spread"/"gap" → population (max-min);
# "lead"/"margin"/"ahead"/"behind"/"clear" → leader (max-second).
_DIFF_CLAIM_RES: Tuple[re.Pattern, ...] = (
    re.compile(
        r"(?<![\w.])(?P<num>\d[\d,]*(?:\.\d+)?)[-\s]point\s+"
        r"(?P<kw>spread|gap|lead|margin)\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?P<kw>spread|gap|lead|margin)\s+of\s+"
        r"(?P<num>\d[\d,]*(?:\.\d+)?)\s+points?\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"(?<![\w.])(?P<num>\d[\d,]*(?:\.\d+)?)\s+points?\s+"
        r"(?P<kw>ahead|behind|clear)\b",
        re.IGNORECASE,
    ),
)

_POPULATION_KEYWORDS = frozenset({"spread", "gap"})

# Percent relative-change claims: "40% faster", "12% more (than)".
_PERCENT_RELATIVE_RE = re.compile(
    r"(?<![\w.])(?P<num>\d[\d,]*(?:\.\d+)?)\s?\\?%\s+"
    r"(?P<kw>more|less|higher|lower|faster|slower|greater|fewer|larger|smaller|"
    r"increase|decrease|improvement|reduction)\b",
    re.IGNORECASE,
)

# Percent proportion claims: "50% of ...".
_PERCENT_PROPORTION_RE = re.compile(
    r"(?<![\w.])(?P<num>\d[\d,]*(?:\.\d+)?)\s?\\?%\s+of\b",
    re.IGNORECASE,
)

# Multiplier claims: "8x speedup", "an 8x improvement", "8x faster".
_MULTIPLIER_CLAIM_RE = re.compile(
    r"(?<![\w.])(?P<num>\d+(?:\.\d+)?)\s?[x×]\s*"
    r"(?P<kw>speedup|speed-up|faster|slower|improvement|increase|reduction|gain)\b",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class Claim:
    """One extracted arithmetic claim."""

    kind: str  # "spread" | "lead" | "percent_relative" | "percent_proportion" | "multiplier"
    value: float
    raw: str
    keyword: str
    start: int
    end: int
    line: int
    paragraph: int
    anchors: frozenset = field(default_factory=frozenset)
    """Nearby content-word tokens (issue #854 lexical-anchor gating).
    Only consumed by proportion-claim validation today; computed for
    every claim uniformly since it's cheap and position-derived."""


def _extract_claims(masked: str, spans: List[Tuple[int, int, int]]) -> List[Claim]:
    claims: List[Claim] = []
    para_bounds = {i: (s, e) for s, e, i in spans}

    def add(kind: str, m: re.Match) -> None:
        paragraph = _paragraph_of(m.start(), spans)
        p_start, p_end = para_bounds.get(paragraph, (0, len(masked)))
        claims.append(
            Claim(
                kind=kind,
                value=_parse_value(m.group("num")),
                raw=m.group(0).strip(),
                keyword=m.group("kw").lower() if "kw" in m.groupdict() and m.group("kw") else kind,
                start=m.start(),
                end=m.end(),
                line=_line_of(m.start(), masked),
                paragraph=paragraph,
                anchors=_anchor_tokens(masked, m.start(), m.end(), p_start, p_end),
            )
        )

    for pattern in _DIFF_CLAIM_RES:
        for m in pattern.finditer(masked):
            kw = m.group("kw").lower()
            kind = "spread" if kw in _POPULATION_KEYWORDS else "lead"
            add(kind, m)
    for m in _PERCENT_RELATIVE_RE.finditer(masked):
        add("percent_relative", m)
    for m in _PERCENT_PROPORTION_RE.finditer(masked):
        add("percent_proportion", m)
    for m in _MULTIPLIER_CLAIM_RE.finditer(masked):
        add("multiplier", m)

    claims.sort(key=lambda c: c.start)
    return claims


# ---------------------------------------------------------------------------
# Tolerance + suppression helpers
# ---------------------------------------------------------------------------


def within_tolerance(claimed: float, computed: float) -> bool:
    """The documented rounding contract: ±1 unit OR ±5% relative."""
    diff = abs(claimed - computed)
    if diff <= ABS_TOLERANCE:
        return True
    if computed != 0 and diff / abs(computed) <= REL_TOLERANCE:
        return True
    return False


def _suppressed_lines(text: str) -> frozenset:
    """1-based line numbers covered by a numeric_consistency lint-disable.

    A directive on line L suppresses claims on line L and line L+1
    (same-line or line-immediately-above placement, per the memo
    lint-disable convention).
    """
    suppressed = set()
    for lineno, line in enumerate(text.splitlines(), start=1):
        for m in _LINT_DISABLE_RE.finditer(line):
            rules = {r.strip() for r in m.group("rules").split(",")}
            if CHECK_NAME in rules:
                suppressed.add(lineno)
                suppressed.add(lineno + 1)
    return frozenset(suppressed)


# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------


@dataclass
class NumericFinding:
    """One numeric-consistency finding against a body claim."""

    code: str            # gap_mismatch | unbridged_population | percent_mismatch | multiplier_mismatch
    severity: str        # "warning" (active) | "info" (suppressed)
    line: int            # 1-based line of the claim
    claim: str           # verbatim claim text
    claimed: float       # the asserted value
    computed: Optional[float]  # the window arithmetic (None when nothing bridges)
    message: str         # human-readable diagnostic with the actual arithmetic
    suppressed: bool = False

    def to_dict(self) -> dict:
        return {
            "code": self.code,
            "severity": self.severity,
            "line": self.line,
            "claim": self.claim,
            "claimed": self.claimed,
            "computed": self.computed,
            "message": self.message,
            "suppressed": self.suppressed,
        }


@dataclass
class NumericConsistencyResult:
    """Outcome of one ``check_numeric_consistency`` pass.

    JSON-serializable + ``Review``-emitter. Shape mirrors
    ``HyperlinkResolverResult`` / ``ConsistencyResult`` so downstream
    aggregation is uniform across the deterministic-checks family.
    """

    version_dir: str
    body_path: str
    numbers_extracted: int = 0
    claims_checked: int = 0
    findings: List[NumericFinding] = field(default_factory=list)

    def passed(self) -> bool:
        """``True`` when no ACTIVE (unsuppressed) findings exist.

        Suppressed (info) findings are recorded but never gate.
        """
        return not any(f.severity == SEVERITY_WARNING for f in self.findings)

    def to_json(self) -> dict:
        return {
            "check": CHECK_NAME,
            "version_dir": self.version_dir,
            "body_path": self.body_path,
            "numbers_extracted": self.numbers_extracted,
            "claims_checked": self.claims_checked,
            "findings": [f.to_dict() for f in self.findings],
            "pass": self.passed(),
        }

    def to_critical_flags(self) -> List[CriticalFlag]:
        """One ``CriticalFlag`` per finding-code cluster (active findings only).

        Only meaningful under ``blocking=True`` — advisory consumers
        never call this. Suppressed findings never contribute.
        """
        flags: List[CriticalFlag] = []
        seen: List[str] = []
        for f in self.findings:
            if f.severity != SEVERITY_WARNING or f.code in seen:
                continue
            seen.append(f.code)
            cluster = [
                x for x in self.findings
                if x.code == f.code and x.severity == SEVERITY_WARNING
            ]
            sample = "; ".join(x.message for x in cluster[:2])
            more = f" (+{len(cluster) - 2} more)" if len(cluster) > 2 else ""
            flags.append(
                CriticalFlag(
                    type=f"{CRITICAL_NUMERIC_INCONSISTENCY}:{f.code}",
                    justification=(
                        f"{len(cluster)} {f.code} numeric-consistency "
                        f"finding(s): {sample}{more}"
                    ),
                    evidence_span=f"{self.body_path}:L{cluster[0].line}",
                )
            )
        return flags

    def to_review(
        self,
        *,
        version_dir: str,
        critic_id: str = CRITIC_ID,
        blocking: bool = False,
    ) -> Review:
        """Build a typed ``Review`` (``kind=Kind.TOOL_EVIDENCE``).

        Advisory (default): one ``Finding`` per :class:`NumericFinding`
        at schema severity ``"minor"`` (active) / ``"nit"``
        (suppressed-info), NO ``CriticalFlag`` — the warn-only model.

        ``blocking=True`` (the essay #460 convergence-blocking hook):
        additionally emits one ``CriticalFlag`` per finding-code cluster
        via :meth:`to_critical_flags`, which forces ``Verdict.BLOCK``
        through ``critics.compute_verdict``. Suppressed findings never
        emit flags.
        """
        scores = [
            Score(
                dimension=CHECK_NAME,
                score=None,
                max=1,
                justification=(
                    "numeric-consistency is a deterministic claim-vs-claim "
                    "arithmetic check; owns no rubric dim."
                ),
            )
        ]
        findings: List[Finding] = []
        for nf in self.findings:
            findings.append(
                Finding(
                    severity="minor" if nf.severity == SEVERITY_WARNING else "nit",
                    dimension=DIM_NUMERIC,
                    evidence_span=f"{self.body_path}:L{nf.line}",
                    rationale=nf.message,
                    suggested_fix=(
                        f"Reconcile the claim {nf.claim!r} with the values "
                        f"named in its surrounding paragraphs — either "
                        f"correct the claimed number or the population it "
                        f"derives from, or suppress with "
                        f"<!-- anvil-lint-disable: {CHECK_NAME} --> and "
                        f"document why the arithmetic is intentional."
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
            critical_flags=self.to_critical_flags() if blocking else [],
        )


# ---------------------------------------------------------------------------
# Claim validation
# ---------------------------------------------------------------------------


def _window(items, paragraph: int):
    """Filter items to the same-paragraph ±1 window."""
    return [t for t in items if abs(t.paragraph - paragraph) <= 1]


def _claim_overlaps(token: NumberToken, claims: List[Claim]) -> bool:
    return any(token.start < c.end and token.end > c.start for c in claims)


def _fmt(v: float) -> str:
    """Compact number formatting for diagnostics (drop trailing .0)."""
    return str(int(v)) if float(v).is_integer() else f"{v:g}"


def _check_diff_claim(
    claim: Claim, candidates: List[NumberToken]
) -> Optional[Tuple[str, Optional[float], str]]:
    """Validate a spread/lead claim. Returns (code, computed, message) or None."""
    values = sorted({t.value for t in candidates}, reverse=True)
    if len(values) < 2:
        return None  # insufficient evidence — conservative silence
    if claim.kind == "spread":
        computed = values[0] - values[-1]
        shape = f"max {_fmt(values[0])} − min {_fmt(values[-1])}"
    else:  # lead / ahead / behind / margin / clear
        computed = values[0] - values[1]
        shape = f"{_fmt(values[0])} − {_fmt(values[1])}"
    if within_tolerance(claim.value, computed):
        return None
    # Unbridged-population: the claim value coincides with a raw window
    # value instead of any difference — the spread-failure shape.
    if any(within_tolerance(claim.value, v) for v in values):
        return (
            UNBRIDGED_POPULATION,
            computed,
            (
                f"claim {claim.raw!r} asserts {_fmt(claim.value)}, which "
                f"matches a raw value in the surrounding window "
                f"({', '.join(_fmt(v) for v in values)}) but no difference "
                f"of window values: {shape} = {_fmt(computed)}. The claimed "
                f"{claim.keyword} appears to be an unbridged population "
                f"value, not a computed difference."
            ),
        )
    return (
        GAP_MISMATCH,
        computed,
        (
            f"claim {claim.raw!r} asserts {_fmt(claim.value)} but the "
            f"window values ({', '.join(_fmt(v) for v in values)}) compute "
            f"{shape} = {_fmt(computed)}, not {_fmt(claim.value)}."
        ),
    )


def _check_proportion_claim(
    claim: Claim, fractions: List[_PairShape]
) -> Optional[Tuple[str, Optional[float], str]]:
    """Validate an "X% of" claim against explicit fraction shapes.

    Issue #854: a percent claim only pairs with a fraction that shares a
    lexical anchor with it (a subject content word present near both),
    UNLESS some fraction in the window already numerically satisfies the
    claim within tolerance — a matching pair is always preferred over a
    mismatching one, regardless of subject, so this preserves the
    pre-#854 "prefer match" behavior exactly. Absent any numeric match,
    a mismatch is only reported against an anchor-sharing fraction; a
    window that contains only unrelated-subject fractions (e.g. "27.3%
    of readable cells" sharing a paragraph with an unrelated "18/18
    pages" fraction) silently skips instead of flagging.
    """
    in_window = [f for f in fractions if abs(f.paragraph - claim.paragraph) <= 1 and f.b != 0]
    if not in_window:
        return None  # no explicit fraction evidence — conservative silence
    for f in in_window:
        pct = f.a / f.b * 100.0
        if within_tolerance(claim.value, pct):
            return None
    anchored = [f for f in in_window if f.anchors & claim.anchors]
    if not anchored:
        return None  # no fraction shares the claim's subject — conservative silence
    best: Optional[_PairShape] = None
    best_pct = 0.0
    for f in anchored:
        pct = f.a / f.b * 100.0
        if best is None or abs(pct - claim.value) < abs(best_pct - claim.value):
            best, best_pct = f, pct
    assert best is not None
    return (
        PERCENT_MISMATCH,
        best_pct,
        (
            f"claim {claim.raw!r} asserts {_fmt(claim.value)}% but the "
            f"window fraction {best.raw.strip()!r} computes "
            f"{_fmt(best.a)} / {_fmt(best.b)} = {best_pct:.1f}%, not "
            f"{_fmt(claim.value)}%."
        ),
    )


def _check_relative_claim(
    claim: Claim, pairs: List[_PairShape]
) -> Optional[Tuple[str, Optional[float], str]]:
    """Validate an "X% more/less/faster" claim against explicit pair shapes."""
    in_window = [p for p in pairs if abs(p.paragraph - claim.paragraph) <= 1]
    if not in_window:
        return None
    best: Optional[_PairShape] = None
    best_pct = 0.0
    best_base = 0.0
    for p in in_window:
        for base in (p.a, p.b):
            if base == 0:
                continue
            pct = abs(p.a - p.b) / abs(base) * 100.0
            if within_tolerance(claim.value, pct):
                return None
            if best is None or abs(pct - claim.value) < abs(best_pct - claim.value):
                best, best_pct, best_base = p, pct, base
    if best is None:
        return None
    # Name the base that produced best_pct — the two base conventions
    # generally disagree, so never imply "either" for a single value.
    return (
        PERCENT_MISMATCH,
        best_pct,
        (
            f"claim {claim.raw!r} asserts {_fmt(claim.value)}% but the "
            f"window pair {best.raw.strip()!r} ({_fmt(best.a)} vs "
            f"{_fmt(best.b)}) computes a {best_pct:.1f}% change "
            f"(base {_fmt(best_base)}), not {_fmt(claim.value)}%."
        ),
    )


def _check_multiplier_claim(
    claim: Claim, pairs: List[_PairShape]
) -> Optional[Tuple[str, Optional[float], str]]:
    """Validate an "Nx speedup" claim against explicit pair shapes."""
    in_window = [p for p in pairs if abs(p.paragraph - claim.paragraph) <= 1]
    if not in_window:
        return None
    best: Optional[_PairShape] = None
    best_ratio = 0.0
    best_num = 0.0
    best_den = 0.0
    for p in in_window:
        for num, den in ((p.a, p.b), (p.b, p.a)):
            if den == 0:
                continue
            ratio = num / den
            if within_tolerance(claim.value, ratio):
                return None
            if best is None or abs(ratio - claim.value) < abs(best_ratio - claim.value):
                best, best_ratio = p, ratio
                best_num, best_den = num, den
    if best is None:
        return None
    # Display the (num, den) that actually produced best_ratio — the
    # closest direction may be min/max, in which case max/min would
    # show arithmetic inconsistent with the quoted result.
    return (
        MULTIPLIER_MISMATCH,
        best_ratio,
        (
            f"claim {claim.raw!r} asserts {_fmt(claim.value)}x but the "
            f"window pair {best.raw.strip()!r} computes "
            f"{_fmt(best_num)} / {_fmt(best_den)} = "
            f"{best_ratio:.1f}x, not {_fmt(claim.value)}x."
        ),
    )


# ---------------------------------------------------------------------------
# Pure-text entry point
# ---------------------------------------------------------------------------


def check_text(text: str, *, latex: bool = False) -> Tuple[List[NumericFinding], int, int]:
    """Run the numeric-consistency check over body text.

    Pure function of the text (no filesystem). Returns
    ``(findings, numbers_extracted, claims_checked)``. Set ``latex=True``
    for ``.tex`` bodies (enables the LaTeX ``%``-comment mask).
    """
    masked = _mask_text(text, latex=latex)
    spans = _paragraph_index(text)
    tokens = _extract_numbers(masked, spans)
    claims = _extract_claims(masked, spans)
    fractions = _extract_shapes(masked, spans, _FRACTION_RES)
    pairs = _extract_shapes(masked, spans, _PAIR_RES)
    suppressed_lines = _suppressed_lines(text)

    findings: List[NumericFinding] = []
    for claim in claims:
        outcome: Optional[Tuple[str, Optional[float], str]] = None
        if claim.kind in ("spread", "lead"):
            # Class segregation: only count-class tokens feed point-diff
            # claims (percent / currency / multiplier never cross-match).
            # Tokens inside any claim span are excluded, and so are
            # tokens that participate in an explicit fraction/pair shape
            # ("47 of 94", "from 120 ms to 15 ms") — those populations
            # are already bridged to their own ratio claims and would
            # only pollute the point-difference arithmetic.
            shape_spans = [(s.start, s.end) for s in fractions + pairs]
            candidates = [
                t
                for t in _window(tokens, claim.paragraph)
                if t.kind == "count"
                and not _claim_overlaps(t, claims)
                and not any(t.start < e and t.end > s for s, e in shape_spans)
            ]
            outcome = _check_diff_claim(claim, candidates)
        elif claim.kind == "percent_proportion":
            outcome = _check_proportion_claim(claim, fractions)
        elif claim.kind == "percent_relative":
            outcome = _check_relative_claim(claim, pairs)
        elif claim.kind == "multiplier":
            outcome = _check_multiplier_claim(claim, pairs)
        if outcome is None:
            continue
        code, computed, message = outcome
        is_suppressed = claim.line in suppressed_lines
        findings.append(
            NumericFinding(
                code=code,
                severity=SEVERITY_INFO if is_suppressed else SEVERITY_WARNING,
                line=claim.line,
                claim=claim.raw,
                claimed=claim.value,
                computed=computed,
                message=(
                    message
                    + (
                        " [suppressed via anvil-lint-disable: "
                        "numeric_consistency]"
                        if is_suppressed
                        else ""
                    )
                ),
                suppressed=is_suppressed,
            )
        )
    return findings, len(tokens), len(claims)


# ---------------------------------------------------------------------------
# Filesystem entry point
# ---------------------------------------------------------------------------


def check_numeric_consistency(
    version_dir: Path, *, body: Optional[Path] = None
) -> NumericConsistencyResult:
    """Run the check against a version directory's body file.

    ``body`` overrides body-file discovery (for adopted-in-place legacy
    threads whose entry point isn't ``<slug>.md``/``main.tex``); when
    omitted, behavior is byte-identical to the historical discovery
    chain. Raises ``FileNotFoundError`` when ``version_dir`` does not
    exist, an override path is missing, or no recognizable body file
    (``<slug>.md`` / ``main.tex``) exists.
    """
    version_dir = Path(version_dir).resolve()
    if not version_dir.is_dir():
        raise FileNotFoundError(
            f"numeric_consistency: version_dir {version_dir!s} does not "
            f"exist or is not a directory."
        )
    body_file = resolve_body_path(
        version_dir, body=body, caller_name="numeric_consistency"
    )
    text = body_file.read_text(encoding="utf-8")
    findings, numbers, claims = check_text(text, latex=body_file.suffix == ".tex")
    return NumericConsistencyResult(
        version_dir=version_dir.name,
        body_path=record_body_path(version_dir, body_file),
        numbers_extracted=numbers,
        claims_checked=claims,
        findings=findings,
    )


def write_review_dir(
    version_dir: Path,
    result: NumericConsistencyResult,
    *,
    critic_id: str = CRITIC_ID,
    blocking: bool = False,
) -> Path:
    """Write ``<version_dir>.numeric/_review.json`` for auto-discovery.

    Delegates to the shared :func:`anvil.lib.sidecar.write_critic_review_dir`
    (issue #1086), which uses ``staged_sidecar`` (issue #350) so the
    sidecar only ever exists in complete form. Because this detector is
    deterministic and cheaply re-runnable, an existing
    ``<version_dir>.numeric/`` from a prior run is removed and
    regenerated (``regenerate=True``, the shared helper's default) — the
    deterministic-regeneration carve-out to the sidecar-immutability
    convention. Returns the path to the written ``_review.json``.
    """
    version_dir = Path(version_dir)
    review = result.to_review(
        version_dir=version_dir.name, critic_id=critic_id, blocking=blocking
    )
    return write_critic_review_dir(version_dir, NUMERIC_SUFFIX, review)


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.numeric_consistency",
        description=(
            "Deterministic numeric-consistency check (claim-vs-claim): "
            "extracts numbers and arithmetic claims (spread/gap/lead, "
            "percent, multiplier) from a version directory's body file "
            "and validates each claim against a same-paragraph (±1) "
            "window. Advisory by default (warn-only)."
        ),
    )
    p.add_argument(
        "version_dir",
        help="Path to <thread>.{N}/ containing <thread>.md or main.tex.",
    )
    p.add_argument(
        "--write-review",
        action="store_true",
        help=(
            "Also write <version_dir>.numeric/_review.json (via "
            "staged_sidecar) for critic-sibling auto-discovery by "
            "aggregate()."
        ),
    )
    p.add_argument(
        "--blocking",
        action="store_true",
        help=(
            "Emit CriticalFlags per finding cluster (forces Verdict.BLOCK "
            "through compute_verdict). Reserved for the essay skill "
            "(#460); advisory consumers (memo/paper) MUST NOT set this."
        ),
    )
    p.add_argument(
        "--body",
        metavar="PATH",
        default=None,
        help=(
            "Override body-file discovery (e.g. for adopted-in-place "
            "legacy threads whose entry point isn't <slug>.md/main.tex, "
            "such as a paper.tex). Relative paths resolve against "
            "version_dir; absolute paths are used as-is. With "
            "--write-review, the resolved portfolio-relative path is "
            "recorded in the sidecar."
        ),
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Returns the process exit code.

    Exit codes:
    - ``0``: clean pass (zero findings, or suppressed-only findings).
    - ``1``: one or more active findings.
    - ``2``: invocation error (missing version_dir or body file).
    """
    parser = _build_cli_parser()
    args = parser.parse_args(argv)
    try:
        result = check_numeric_consistency(
            Path(args.version_dir),
            body=Path(args.body) if args.body else None,
        )
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result.to_json(), indent=2))
    if args.write_review:
        out = write_review_dir(
            Path(args.version_dir), result, blocking=args.blocking
        )
        print(f"wrote {out}", file=sys.stderr)
    return 0 if result.passed() else 1


__all__ = [
    "CRITIC_ID",
    "CHECK_NAME",
    "DIM_NUMERIC",
    "NUMERIC_SUFFIX",
    "CRITICAL_NUMERIC_INCONSISTENCY",
    "GAP_MISMATCH",
    "UNBRIDGED_POPULATION",
    "PERCENT_MISMATCH",
    "MULTIPLIER_MISMATCH",
    "SEVERITY_WARNING",
    "SEVERITY_INFO",
    "ABS_TOLERANCE",
    "REL_TOLERANCE",
    "NumberToken",
    "Claim",
    "NumericFinding",
    "NumericConsistencyResult",
    "within_tolerance",
    "check_text",
    "check_numeric_consistency",
    "write_review_dir",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
