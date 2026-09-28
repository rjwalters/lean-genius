"""Static lint pass that mirrors the marp-vscode `slide-content-overflow` diagnostic.

This module is a Python port of the upstream diagnostic introduced in
marp-team/marp-vscode (see https://github.com/marp-team/marp-vscode/issues/519
and the diagnostic file
`src/diagnostics/preview/slide-content-overflow.ts`). The upstream
implementation is **DOM-based**: it inspects the rendered preview's
`section.scrollHeight > section.clientHeight` and
`section.scrollWidth > section.clientWidth`. That cannot run statically in a
markdown pipeline — so this port re-implements the same conceptual rule
("does the slide content exceed the safe area?") as a deterministic capacity
budget over the markdown source.

Upstream port pin
-----------------
- repo:    marp-team/marp-vscode
- file:    src/diagnostics/preview/slide-content-overflow.ts
- sha:     3b8617431867b68f4241c453ae2c7601a4298aa8
- rule(s): slide-content-overflow  (the only diagnostic ported in this seed)

When upstream evolves (additional diagnostics, refined heuristics in the
runtime DOM tracker, etc.), follow-up work should:

1. Re-fetch the upstream file at a newer SHA.
2. Update the SHA pin above.
3. Add new rules to ``_RULES`` below if they map cleanly onto a static check.

Anvil-specific design choices vs. upstream
------------------------------------------
- **Static, not DOM.** Upstream measures the actual rendered slide;
  this port estimates capacity from the markdown source. As a result, the
  Anvil rule is conservative — it catches the obvious overflow patterns
  (the #24 figure + 4 bullets repro and the #25 `_class: ask` H1 + H2 repro
  exhaustively) but defers borderline cases to the VLM critic in issue #30.
- **Severity mapping is stricter.** Upstream emits ``Warning``; in the Anvil
  pipeline the rule is wired as a review-phase hard-fail (per the curator
  addendum on issue #31). The severity returned by ``lint_deck`` is
  ``"error"`` when the capacity overage is clear, ``"warning"`` when borderline,
  and ``"info"`` only as a suppressed result of the
  ``anvil-lint-disable: slide-content-overflow`` escape hatch.
- **Geometry constants** are pulled from
  ``anvil/skills/deck/assets/anvil-deck.css`` and the equivalent slides
  theme: 16:9, 1280×720, padding 56/72, base font 26px, line-height 1.45.
  These constants live at module scope so a consumer with a custom theme can
  override them via the public API (``lint_deck(path, geometry=...)``).
- **Consumer-theme capacity contract (issue #1150).** The constants above
  are calibrated against the *shipped* ``anvil-deck`` theme only — a
  registered consumer theme (``--theme-set`` / frontmatter ``theme:``) with
  different padding, base font size, or ``_class: ask`` treatment silently
  diverges from this model, producing false-positive (or mis-calibrated)
  ``slide-content-overflow`` findings. Rather than parse the theme's CSS
  wholesale, a consumer theme states its own geometry via a structured
  ``/* @anvil-capacity ... */`` comment block in the theme's own CSS file;
  :func:`geometry_from_theme_css` / :func:`geometry_from_theme_contract`
  parse that block into a :class:`Geometry` override, and the caller passes
  it to ``lint_deck(path, geometry=...)``. A theme with no such block (or
  the shipped theme itself) is unaffected — the default :class:`Geometry`
  is used exactly as before. See ``anvil/lib/snippets/brand-theme-porting.md``
  §"Declaring capacity geometry" for the consumer-facing contract
  documentation.
- **Escape hatch.** A per-slide HTML comment of the form
  ``<!-- anvil-lint-disable: slide-content-overflow -->`` suppresses the
  rule for that one slide; the finding is downgraded to ``info`` so the
  reviser still sees that the slide is dense but ``advance`` is not blocked.
  The deck skill documents when applying it is sanctioned (issue #965):
  a singleton-``_class:`` slide — typically the one ``title`` slide, which
  the post-render ``auto_shrink_detector`` peer-relative rule structurally
  cannot cross-check — may be suppressed only after ``deck-vision``'s v1
  ``vertical_overflow`` reads the rendered PNG clean, with that citation
  recorded. See ``anvil/skills/deck/commands/deck-revise.md`` step 7c.
- **Aspect- and CSS-aware capacity model (issue #622).** Two refinements
  brought the source-side estimate into agreement with the rendered PDF on
  keyword-less decks (the default drafter output), where the flat charges
  over-fired at ~75%. (1) A keyword-less standalone image whose file is
  locally resolvable relative to the deck is charged its *width-normalized
  rendered height* (read from the PNG's IHDR via stdlib ``struct`` — no new
  dependency), capped at the flat ``image_units`` fallback: a wide-aspect
  mermaid PNG renders far shorter than a square one. (2) A ``<div class="X">``
  whose class is defined ``display:flex`` / ``display:grid`` in the
  frontmatter ``style:`` block has its children re-costed and scaled by
  ``flex_container_cost_factor`` (columns render side-by-side, not stacked).
  Both refinements only *reduce* charges; they add no new error sources.
  Any layout the heuristic still mis-scores keeps the escape hatch above.

Anvil-specific scope
--------------------
- Only the ``slide-content-overflow`` rule is ported from upstream. The
  ``image-resource``, ``frontmatter-deprecated-syntax``, and other
  marp-vscode rules are not ported (they are either irrelevant to Anvil's
  pipeline or out of scope for this iteration).
- The ``figure-italic-supporting-line-too-long`` rule is **Anvil-original**
  (no marp-vscode upstream). It detects a long italic supporting line
  directly under a standalone figure block — the figure-idiom regression
  documented in issues #100 / #101. Authors fold what would have been three
  bullets into one italic sentence; the sentence wraps to 2-3 rendered lines
  and clips at the slide bottom on 16:9 because italic glyph width is ~5%
  wider than upright body weight and the caption margins eat additional
  vertical space. The threshold (18 words OR 108 characters) is anchored
  against the shipped ``clean_figure_plus_supporting_line.md`` fixture and
  the canary regressions from the post-#68 re-render wave (bower.v2 slides
  7/10, citation-clear.v2 slides 7/8, bibliotype.v2 slide 7 — all 25-32
  words). Severity is ``warning`` (the check is a heuristic for *likely*
  overflow; the upstream-derived ``slide-content-overflow`` rule remains
  the authoritative hard-fail capacity check).
- The ``inline-display-style-dropped`` rule is **Anvil-original** (no
  marp-vscode upstream). It detects inline ``style="...display:(grid|flex|
  inline-grid|inline-flex)..."`` attributes in the deck markdown source.
  Marp renders slide content into a ``<foreignObject>`` element inside an
  SVG and rasterizes via Chromium for the canonical ``--pdf`` output;
  through that path, inline ``display:`` rules are silently dropped — the
  slide compiles cleanly but multi-column layouts flatten to single-column
  stacked output (verified by studio's ikebot.3 canary, 2026-05-30; see
  issue #128). The reliable workaround is a frontmatter ``style: |`` block
  defining a CSS class, then ``<div class="...">`` in the slide body —
  class-based selectors apply via the global stylesheet, which the
  foreignObject path does honor. Severity is ``warning`` (the static check
  catches the source pattern but cannot verify the PDF render; the
  ``deck-vision`` VLM critic is authoritative on actual rendered layout).

Public API
----------
``lint_deck(path) -> LintResult``
    Run the lint over a single ``deck.md`` file. Returns errors/warnings/infos
    keyed to slide number and source line.

Promoted to ``anvil/lib/`` per issue #318; both skill-side modules
(``anvil/skills/deck/lib/marp_lint.py`` and
``anvil/skills/slides/lib/marp_lint.py``) are now thin re-exports of this
canonical implementation. The previous ``importlib.util.spec_from_file_location``
shim in the slides skill (the install-order fragility that fired when slides
was installed without deck) is gone — consumers ``from anvil.lib.marp_lint
import …`` directly.
"""

from __future__ import annotations

import re
import struct
from dataclasses import dataclass, field, fields, replace
from pathlib import Path


# Module-level metadata --------------------------------------------------------

#: Upstream commit SHA the ported diagnostic is derived from.
UPSTREAM_SHA: str = "3b8617431867b68f4241c453ae2c7601a4298aa8"

#: List of rules implemented in this module. ``slide-content-overflow`` is
#: ported from marp-vscode (see ``UPSTREAM_SHA``); ``figure-italic-supporting-
#: line-too-long`` is Anvil-original (derived from #100 / #101 / canary
#: regressions — see module docstring "Anvil-specific scope"). The
#: ``inline-display-style-dropped`` rule is also Anvil-original (derived
#: from issue #128 / studio's ikebot.3 canary — see module docstring).
PORTED_RULES: tuple[str, ...] = (
    "slide-content-overflow",
    "figure-italic-supporting-line-too-long",
    "inline-display-style-dropped",
)


# Slide-geometry model ---------------------------------------------------------


@dataclass(frozen=True)
class Geometry:
    """Slide geometry + content-cost constants used by the capacity model.

    Defaults match ``anvil/skills/deck/assets/anvil-deck.css`` and the slides
    theme. ``line_units_per_slide`` is the **vertical content budget**: the
    number of 1.0-unit body lines that fit in the safe area after subtracting
    padding. Every content element below contributes a fractional or integer
    number of line units; the slide overflows when the sum exceeds the budget.

    A "line unit" is calibrated to one body-text line at 26px/1.45 line-height
    plus its tight inter-paragraph spacing — empirically ~40px of vertical
    advance. The budget is the floor of ``(720 - top_pad - bottom_pad) / 40``,
    which lands at 14 line units for the default 56/56 padding. We round down
    by 1 for safety (the budget is 13 in the model below) because horizontal
    word wrap can spill an extra line, and the upstream rule is conservative
    about false-negatives, not false-positives.
    """

    # Pixel geometry — provided for documentation; capacity is in line units.
    slide_width_px: int = 1280
    slide_height_px: int = 720
    top_padding_px: int = 56
    bottom_padding_px: int = 56
    body_line_height_px: int = 40  # 26px font * 1.45 + half of the 16px p-margin

    # Capacity budget (line units). Errors are emitted only when the overage
    # is at least ``error_threshold_units`` above the budget; otherwise it's a
    # warning. This is the source-level analogue of "scrollHeight exceeds
    # clientHeight by more than a trivial amount" — we don't want to fire on
    # a slide that's one wrapped-bullet over budget.
    capacity_units: float = 13.0
    error_threshold_units: float = 1.5
    warning_threshold_units: float = 0.0  # any overage at all gets a warning

    # Per-element costs, in line units.
    h1_units: float = 3.2   # 56px font × 1.15 + 24px margin ≈ 88px (hero on default;
                            # on `_class: ask` the H1 is 60px and even taller; this
                            # is intentionally conservative so the #25 H2+H1+bullets
                            # repro hits the error threshold)
    h2_units: float = 2.0   # 40px font × 1.2  + 28px margin ≈ 76px ≈ 2.0 lines
    h3_units: float = 1.6   # 28px font × 1.3  + 24px margin ≈ 60px ≈ 1.6 lines
    h4_plus_units: float = 1.3
    body_paragraph_units: float = 1.0       # one wrapped line of body text
    extra_body_wrap_units: float = 1.0      # per ~70-char overflow of a paragraph
    body_paragraph_chars_per_line: int = 70
    bullet_units: float = 1.1               # bullet line + tight spacing
    bullet_continuation_units: float = 0.6  # wrapped bullet continuation
    bullet_chars_per_line: int = 64
    nested_bullet_units: float = 1.0
    code_block_overhead_units: float = 1.6  # padding + margin around <pre>
    code_line_units: float = 0.7            # code lines are denser (smaller font)
    table_header_units: float = 1.6
    table_row_units: float = 1.1
    blockquote_units: float = 1.2
    image_units: float = 7.0                # a full-width PNG eats ~half the slide
    image_small_units: float = 3.0          # if an explicit width hint < 50% is given
    horizontal_rule_units: float = 0.5
    hr_inside_slide_units: float = 0.5
    paragraph_break_units: float = 0.4      # the gap between block elements

    # Anti-pattern penalties applied at slide level after the per-element sum.
    # The H1+H2 combination is a documented overflow source on `_class: ask`
    # slides (issue #25): having both a section tag and a hero headline burns
    # vertical space the slide does not have. We surface this as an extra
    # capacity charge rather than rule out the combination outright (the
    # drafter may use it intentionally on a generous slide).
    h1_plus_h2_penalty_units: float = 1.5

    # `_class: ask` slides use heavier padding (80px vs 56px) per
    # anvil-deck.css, so the safe area is ~96px smaller — about 2.4 line
    # units. We subtract this from capacity rather than from the cost so the
    # finding message still reports the slide's content total honestly.
    ask_class_capacity_penalty_units: float = 2.4

    # Budget for an italic supporting line directly under a standalone figure
    # block (the post-#68 "figure + ONE italic line" idiom — see
    # ``assets/slide-archetypes.md`` "Figure layout idioms"). The two
    # thresholds fire as a logical **OR**: a line longer than EITHER bound
    # is flagged.
    #
    # - 18 words: 18 × ~5 chars + spaces ≈ 108 chars. Anchored against the
    #   shipped ``clean_figure_plus_supporting_line.md`` fixture (originally
    #   17 words / 124 chars; tightened to ≤108 chars in the same PR that
    #   introduced this rule). Catches the bower / citation-clear /
    #   bibliotype canary regressions (25-32 words) with comfortable
    #   headroom.
    # - 108 chars: italic glyphs are ~5% wider than upright body weight; the
    #   ``body_paragraph_chars_per_line = 70`` constant above implies a
    #   two-line wrap kicks in around ~134 italic chars. 108 leaves a ~20%
    #   safety margin (matches the ``capacity_units = 13`` vs raw 14-unit
    #   budget margin elsewhere in this Geometry).
    #
    # A consumer with a wider safe area or smaller body font overrides via
    # the existing ``lint_deck(path, geometry=Geometry(...))`` parameter.
    italic_supporting_line_max_words: int = 18
    italic_supporting_line_max_chars: int = 108

    # Cost multiplier applied to the accumulated sequential cost of content
    # inside a frontmatter-CSS flex/grid container (issue #622). The
    # sequential capacity model stacks every element's vertical cost, but a
    # ``display:flex`` / ``display:grid`` container renders its children
    # side-by-side (sharing horizontal space) — so the true vertical extent
    # is a fraction of the stacked sum. ``0.5`` assumes two roughly-equal
    # columns (the ``title-row`` / two-column idiom that inherited from
    # 40/40 decks and drove the seed-deck.1 slides-1-and-13 false positives).
    # A consumer with three-column layouts can push this lower via the
    # ``lint_deck(path, geometry=Geometry(...))`` override; the per-slide
    # ``<!-- anvil-lint-disable: slide-content-overflow -->`` escape hatch
    # remains the override for any layout the heuristic still gets wrong.
    flex_container_cost_factor: float = 0.5


_DEFAULT_GEOMETRY = Geometry()


# Consumer-theme capacity-override contract (issue #1150) ----------------------
#
# A registered consumer theme (see ``anvil/lib/snippets/brand-theme-porting.md``)
# can declare its own capacity geometry via a structured comment block
# anywhere in its CSS file:
#
#     /* @anvil-capacity
#        top_padding_px: 72
#        bottom_padding_px: 72
#        body_line_height_px: 44
#        capacity_units: 12.0
#        ask_class_capacity_penalty_units: 1.8
#     */
#
# Any :class:`Geometry` field name is a valid key — the block is a sparse
# override, not a full re-specification: fields the block omits keep their
# shipped ``anvil-deck`` default. This lets a consumer state only the few
# properties their brand port actually changed (padding, base font/line
# height, the `_class: ask` capacity delta) without reproducing every
# per-element cost constant.
#
# The contract is deliberately declarative-and-forgiving, matching the
# framework's "graceful degrade for opt-in overrides" pattern
# (``anvil/lib/theme.py``'s ``load_theme`` docstring names the same
# convention): an unknown key, an unparseable value, or a missing block
# entirely all fall back to the shipped default rather than raising —
# a malformed contract must never crash the lint, only under-calibrate it
# back to the shipped-theme baseline.

_CAPACITY_CONTRACT_RE = re.compile(
    r"/\*\s*@anvil-capacity\b(?P<body>.*?)\*/",
    re.DOTALL,
)

#: Maps each ``Geometry`` field name to its declared type (``int`` or
#: ``float``), derived once from the dataclass so the contract parser never
#: hardcodes the field list separately from ``Geometry`` itself.
_GEOMETRY_FIELD_TYPES: dict[str, type] = {
    f.name: (int if f.type == "int" else float) for f in fields(Geometry)
}


@dataclass(frozen=True)
class ThemeCapacityContract:
    """Result of resolving a consumer theme's ``@anvil-capacity`` contract.

    ``geometry`` is always usable directly as ``lint_deck(path,
    geometry=result.geometry)`` — it equals ``Geometry()`` (the shipped
    default) whenever no contract block was found, the block was empty, or
    every key in it was unrecognized/unparseable.
    """

    geometry: Geometry
    found: bool
    overrides: dict = field(default_factory=dict)
    warnings: tuple[str, ...] = ()


def geometry_from_theme_css(css_source: str) -> ThemeCapacityContract:
    """Parse a consumer theme's ``/* @anvil-capacity ... */`` block.

    Scans ``css_source`` (the full text of a theme CSS file) for the first
    ``@anvil-capacity`` comment block and parses ``key: value`` lines from
    its body (block-comment ``*`` continuation prefixes and trailing ``;``
    are tolerated). Each key must name a :class:`Geometry` field; unknown
    keys and unparseable values are recorded in ``warnings`` and skipped —
    they never raise and never invalidate the other keys in the same block.

    Returns a :class:`ThemeCapacityContract` whose ``geometry`` is the
    shipped default :class:`Geometry` with the parsed overrides applied
    (``found=False`` and ``geometry == Geometry()`` when no block exists).
    """
    match = _CAPACITY_CONTRACT_RE.search(css_source)
    if not match:
        return ThemeCapacityContract(geometry=_DEFAULT_GEOMETRY, found=False)

    overrides: dict[str, int | float] = {}
    warnings: list[str] = []
    for raw_line in match.group("body").splitlines():
        line = raw_line.strip()
        if line.startswith("*"):
            line = line[1:].strip()
        line = line.rstrip(";").strip()
        if not line:
            continue
        if ":" not in line:
            warnings.append(f"ignored malformed line (no ':'): {line!r}")
            continue
        key, _, raw_value = line.partition(":")
        key = key.strip()
        raw_value = raw_value.strip().rstrip(";").strip()
        field_type = _GEOMETRY_FIELD_TYPES.get(key)
        if field_type is None:
            warnings.append(f"ignored unknown geometry field {key!r}")
            continue
        try:
            overrides[key] = field_type(raw_value)
        except (TypeError, ValueError):
            warnings.append(
                f"ignored {key!r}: could not parse {raw_value!r} as "
                f"{field_type.__name__}"
            )
            continue

    if not overrides:
        return ThemeCapacityContract(
            geometry=_DEFAULT_GEOMETRY, found=True, warnings=tuple(warnings)
        )

    geometry = replace(_DEFAULT_GEOMETRY, **overrides)
    return ThemeCapacityContract(
        geometry=geometry,
        found=True,
        overrides=overrides,
        warnings=tuple(warnings),
    )


def geometry_from_theme_contract(
    css_path: Path | str | None,
) -> ThemeCapacityContract:
    """Resolve capacity geometry from a consumer theme CSS file on disk.

    Absence-tolerant, per the framework's graceful-degrade convention: a
    ``None`` path, a missing file, or an unreadable file all return the
    shipped default (``found=False``) rather than raising. Pass the result's
    ``geometry`` straight to ``lint_deck(path, geometry=...)``.
    """
    if css_path is None:
        return ThemeCapacityContract(geometry=_DEFAULT_GEOMETRY, found=False)
    path = css_path if isinstance(css_path, Path) else Path(css_path)
    if not path.is_file():
        return ThemeCapacityContract(geometry=_DEFAULT_GEOMETRY, found=False)
    try:
        css_source = path.read_text(encoding="utf-8")
    except OSError:
        return ThemeCapacityContract(geometry=_DEFAULT_GEOMETRY, found=False)
    return geometry_from_theme_css(css_source)


# Result types -----------------------------------------------------------------


@dataclass
class Finding:
    """A single lint hit. Schema matches AC1 on issue #31."""

    slide: int
    line: int
    rule: str
    severity: str  # "error" | "warning" | "info"
    message: str

    def to_dict(self) -> dict:
        return {
            "slide": self.slide,
            "line": self.line,
            "rule": self.rule,
            "severity": self.severity,
            "message": self.message,
        }


@dataclass
class LintResult:
    errors: list[Finding] = field(default_factory=list)
    warnings: list[Finding] = field(default_factory=list)
    infos: list[Finding] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.errors) + len(self.warnings) + len(self.infos)

    def to_summary(self) -> dict:
        """Shape that fits cleanly into the review ``_summary.md`` ``lint`` block."""
        return {
            "ran": True,
            "errors": len(self.errors),
            "warnings": len(self.warnings),
            "infos": len(self.infos),
            "errors_by_slide": [f.to_dict() for f in self.errors],
            "warnings_by_slide": [f.to_dict() for f in self.warnings],
        }


# Slide parsing ----------------------------------------------------------------


@dataclass
class _Slide:
    index: int          # 1-based slide number
    start_line: int     # 1-based line in the source file
    end_line: int       # 1-based, inclusive
    raw: str            # full slide source including any leading directives
    body: str           # source with leading frontmatter / directive lines stripped


# Matches Marp's slide separator: a `---` on its own line. We use this also as
# the YAML-frontmatter terminator at file head; the first occurrence may be the
# end of frontmatter rather than a slide break.
_SLIDE_BREAK_RE = re.compile(r"^---\s*$", re.MULTILINE)

# Marp per-slide directive comment, e.g.
#   <!-- _class: ask -->
#   <!-- _backgroundColor: black -->
# Also matches anvil's escape-hatch directive.
_DIRECTIVE_COMMENT_RE = re.compile(
    r"^\s*<!--\s*(?P<body>[^>]+?)\s*-->\s*$", re.MULTILINE
)

# Anvil per-slide lint suppression directive.
_LINT_DISABLE_RE = re.compile(
    r"^\s*<!--\s*anvil-lint-disable:\s*(?P<rules>[a-zA-Z0-9_,\-\s]+?)\s*-->\s*$",
    re.MULTILINE,
)


def _split_slides(source: str) -> list[_Slide]:
    """Split a Marp ``deck.md`` source into one record per slide.

    Handles the YAML frontmatter convention: if the file opens with ``---``,
    the next ``---`` is the close of frontmatter, **not** a slide break.
    """
    lines = source.splitlines()
    n = len(lines)

    # Detect frontmatter and find its end.
    start_idx = 0
    if n > 0 and lines[0].strip() == "---":
        # find the matching close
        for j in range(1, n):
            if lines[j].strip() == "---":
                start_idx = j + 1
                break

    # Now slice on subsequent `---` lines (slide breaks).
    slides: list[_Slide] = []
    current_start = start_idx
    slide_num = 0
    i = start_idx
    while i < n:
        if lines[i].strip() == "---":
            # close out the current slide
            slide_num += 1
            raw = "\n".join(lines[current_start:i])
            slides.append(
                _Slide(
                    index=slide_num,
                    start_line=current_start + 1,
                    end_line=i,  # exclusive of the break itself; 1-based
                    raw=raw,
                    body=raw,
                )
            )
            current_start = i + 1
        i += 1

    # tail slide (no trailing `---`)
    if current_start < n:
        slide_num += 1
        raw = "\n".join(lines[current_start:n])
        if raw.strip():
            slides.append(
                _Slide(
                    index=slide_num,
                    start_line=current_start + 1,
                    end_line=n,
                    raw=raw,
                    body=raw,
                )
            )

    # Drop any slides that are pure whitespace / pure directive comments.
    pruned: list[_Slide] = []
    next_num = 1
    for s in slides:
        if _is_effectively_empty(s.raw):
            continue
        pruned.append(
            _Slide(
                index=next_num,
                start_line=s.start_line,
                end_line=s.end_line,
                raw=s.raw,
                body=s.raw,
            )
        )
        next_num += 1
    return pruned


def _is_effectively_empty(slide_src: str) -> bool:
    """A slide is empty if every non-blank line is a directive comment."""
    for line in slide_src.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if _DIRECTIVE_COMMENT_RE.match(line):
            continue
        return False
    return True


# Capacity model ---------------------------------------------------------------


@dataclass
class _CostBreakdown:
    total_units: float = 0.0
    parts: list[tuple[str, float]] = field(default_factory=list)
    heading_levels: list[int] = field(default_factory=list)

    def add(self, label: str, units: float) -> None:
        self.total_units += units
        self.parts.append((label, units))


# Detect a `_class: ask` directive on the slide.
_CLASS_ASK_RE = re.compile(
    r"^\s*<!--\s*_class:\s*ask\s*-->\s*$", re.MULTILINE
)

# Anchored variant of the image regex: matches a STANDALONE figure block —
# a single `![alt](path)` reference that is the entire line (modulo
# surrounding whitespace), regardless of alt-text length. Used as the
# trigger for the ``figure-italic-supporting-line-too-long`` rule, where
# only a standalone figure block (not an inline image in a paragraph) sets
# up the "figure + italic supporting line" idiom, and (since #905) as the
# standalone-image gate in ``_accumulate_line_costs``'s
# ``slide-content-overflow`` cost model — keyed on line *structure*, not
# ``len(raw_line)``, so a long, accessible alt string can't push a
# standalone image into the body-paragraph branch and get double-charged
# (alt text is never rendered on the slide).
_STANDALONE_FIGURE_RE = re.compile(r"^\s*!\[[^\]]*\]\([^)]*\)\s*$")

# Single ``_..._`` or ``*...*`` italic delimiter spanning the WHOLE stripped
# line. The inner character class ``[^_*]`` deliberately rejects
# bold-italic (``**_..._**`` / ``_**...**_``) and adjacent emphasis runs:
# those are content emphasis patterns, not figure supporting lines.
_FULL_LINE_ITALIC_RE = re.compile(
    r"^\s*[_*]([^_*][^_*\n]*?)[_*]\s*$"
)


# Detect inline ``style="...display:(grid|flex|inline-grid|inline-flex)..."``
# (and the single-quoted variant). Used by the
# ``inline-display-style-dropped`` rule. The pattern accepts optional
# whitespace around the ``:`` and is case-insensitive so it catches
# ``DISPLAY:Grid`` etc. The value is captured for the diagnostic message.
_INLINE_DISPLAY_STYLE_DQ_RE = re.compile(
    r"""style\s*=\s*"[^"]*?display\s*:\s*(?P<value>inline-grid|inline-flex|grid|flex)\b[^"]*"
    """,
    re.IGNORECASE | re.VERBOSE,
)
_INLINE_DISPLAY_STYLE_SQ_RE = re.compile(
    r"""style\s*=\s*'[^']*?display\s*:\s*(?P<value>inline-grid|inline-flex|grid|flex)\b[^']*'
    """,
    re.IGNORECASE | re.VERBOSE,
)

_FENCED_OPEN_RE = re.compile(r"^\s*(```|~~~)")
_HEADING_RE = re.compile(r"^(#{1,6})\s+(.*)$")
_BULLET_RE = re.compile(r"^(\s*)([-*+]|\d+[.)])\s+(.*)$")
_IMAGE_RE = re.compile(r"!\[[^\]]*\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")

# Captures the alt-string of an image so callers can scan it for Marp sizing
# keywords. The alt-string is the bracketed text between ``![`` and ``](``;
# Marp keyword sizing (``bg``, ``bg right:N%``, ``h:NNNpx``, ``w:N%``, …)
# lives entirely inside this region. See ``_image_cost_units`` below for the
# keyword parser that consumes the captured alt text.
_IMAGE_ALT_RE = re.compile(r"!\[(?P<alt>[^\]]*)\]")

# Marp ``bg`` keyword in the alt-string: matches ``bg`` as a whole token. The
# load-bearing forms are ``bg``, ``bg right:N%``, ``bg left:N%``, ``bg vertical:N%``
# (split-panel backgrounds). All ``bg`` forms paint into the slide background
# and consume zero vertical body flow.
_IMAGE_BG_KEYWORD_RE = re.compile(r"(?:^|\s)bg(?:\s|$|:)")

# Marp explicit-height keyword in the alt-string: ``h:NNNpx`` or ``h:NN%``.
# Documented at https://marpit.marp.app/image-syntax — the ``h:`` keyword
# clamps the rendered image's vertical extent; we use it to compute the
# slide's actual vertical body-flow cost.
_IMAGE_HEIGHT_KEYWORD_RE = re.compile(
    r"(?:^|\s)h[:= ](?P<height>\d+(?:%|px))(?:\s|$)"
)

# Marp explicit-width keyword in the alt-string: ``w:NNNpx`` or ``w:NN%``.
# Used as a secondary heuristic — only consulted when no ``h:`` keyword is
# present, since width alone is a weak proxy for vertical cost.
_IMAGE_WIDTH_KEYWORD_RE = re.compile(
    r"(?:^|\s)w[:= ](?P<width>\d+(?:%|px))(?:\s|$)"
)
_HR_RE = re.compile(r"^\s*(\*\s*){3,}\s*$|^\s*(-\s*){3,}\s*$|^\s*(_\s*){3,}\s*$")
_BLOCKQUOTE_RE = re.compile(r"^\s*>")
_TABLE_SEP_RE = re.compile(r"^\s*\|?[\s:|-]+\|[\s:|-]*$")
_TABLE_ROW_RE = re.compile(r"^\s*\|.*\|\s*$")

# A ``<div ... class="X Y Z">`` opening tag (issue #622). The captured group
# is the raw class attribute value (possibly space-separated multi-class);
# callers intersect it against the frontmatter-declared flex/grid class set.
_DIV_CLASS_OPEN_RE = re.compile(
    r"<div\b[^>]*\bclass\s*=\s*[\"']([^\"']+)[\"']", re.IGNORECASE
)
# Any ``<div`` open / ``</div>`` close token, for depth tracking.
_DIV_OPEN_TOKEN_RE = re.compile(r"<div\b", re.IGNORECASE)
_DIV_CLOSE_TOKEN_RE = re.compile(r"</div\s*>", re.IGNORECASE)

# A URL-scheme prefix (``https://``, ``http://``, ``ftp://``, …) or a
# ``data:`` URI — image references we must NOT try to resolve on the local
# filesystem (issue #622).
_URL_SCHEME_RE = re.compile(r"^(?:[a-zA-Z][a-zA-Z0-9+.\-]*://|data:)")

# Frontmatter-CSS class whose ruleset declares a flex/grid display mode
# (issue #622). Matches ``.two-col { ... display: flex ... }`` etc. — only
# the class name is captured; the full CSS is not parsed.
_FLEX_CLASS_RE = re.compile(
    r"\.([\w-]+)\s*\{[^}]*display\s*:\s*(?:inline-flex|inline-grid|flex|grid)\b",
    re.IGNORECASE,
)

#: 8-byte PNG file signature (the fixed magic prefix of every PNG file).
_PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"


def _read_png_dimensions(path: Path) -> tuple[int, int] | None:
    """Read a PNG's pixel (width, height) from its IHDR chunk, stdlib-only.

    The PNG spec fixes the layout of the first 24 bytes: an 8-byte signature,
    a 4-byte IHDR length, the 4-byte ``IHDR`` chunk type, then the 4-byte
    width and 4-byte height (big-endian unsigned). We only need those 24
    bytes — no image decode, no Pillow. Returns ``None`` (never raises) on any
    failure: short read, wrong signature, unpack error. See issue #622.
    """
    try:
        with open(path, "rb") as fh:
            header = fh.read(24)
        if len(header) < 24 or header[:8] != _PNG_SIGNATURE:
            return None
        width, height = struct.unpack(">II", header[16:24])
        return (int(width), int(height))
    except (OSError, struct.error, ValueError):
        return None


def _resolve_image_dimensions(
    image_path: str, deck_path: Path
) -> tuple[int, int] | None:
    """Resolve an image reference relative to the deck file and read its size.

    Returns ``(width, height)`` in pixels, or ``None`` on any failure:
    URL/data-URI scheme (not a local file), unresolvable path, missing file,
    unsupported format (only PNG is parsed — mermaid output is always PNG),
    or a parse error. All failure modes fall back to the flat image charge in
    the caller. See issue #622.
    """
    try:
        if not image_path or _URL_SCHEME_RE.match(image_path):
            return None
        resolved = (deck_path.parent / image_path).resolve()
        if not resolved.is_file():
            return None
        return _read_png_dimensions(resolved)
    except (OSError, ValueError):
        return None


def _extract_frontmatter(source: str) -> str:
    """Return the raw text between the opening and closing ``---`` fences.

    Empty string when the source has no YAML frontmatter. Used to scan the
    deck-wide ``style:`` CSS block for flex/grid class definitions (#622).
    """
    lines = source.splitlines()
    if not lines or lines[0].strip() != "---":
        return ""
    for j in range(1, len(lines)):
        if lines[j].strip() == "---":
            return "\n".join(lines[1:j])
    return ""


def _collect_flex_class_names(source: str) -> frozenset[str]:
    """Extract class names whose frontmatter CSS ruleset declares flex/grid.

    A ``display:flex`` / ``display:grid`` (and the ``inline-`` variants)
    container renders its children side-by-side, so the sequential capacity
    model over-counts a slide that stacks two columns. We scan only the YAML
    frontmatter ``style:`` block (read once per ``lint_source`` call) with a
    lightweight regex — no CSS parser dependency. See issue #622.
    """
    frontmatter = _extract_frontmatter(source)
    if not frontmatter:
        return frozenset()
    return frozenset(m.group(1) for m in _FLEX_CLASS_RE.finditer(frontmatter))


def _image_cost_units(
    alt_text: str,
    geo: Geometry,
    *,
    image_path: str | None = None,
    deck_path: Path | None = None,
) -> tuple[float, str]:
    """Estimate the vertical body-flow cost of a Marp image from its alt-string.

    Returns a ``(units, label)`` tuple. The label is a short tag used by the
    cost-breakdown roll-up so a reviser reading the lint message can see WHY
    the cost was charged as it was.

    Marp's image-syntax keywords (https://marpit.marp.app/image-syntax) live
    inside the alt-string between ``![`` and ``](``. The load-bearing
    keywords for the capacity model:

    - ``bg`` (and the panel variants ``bg right:N%`` / ``bg left:N%`` /
      ``bg vertical:N%``) — paints into the slide background. Consumes
      **zero** vertical body-flow units. The image lives behind the body
      content, not inside it.
    - ``h:NNNpx`` / ``h:NN%`` — explicit vertical clamp. We translate the
      pixel/percent height directly to line units using
      ``geo.body_line_height_px`` (px → units) or ``geo.capacity_units``
      (% → units).
    - ``w:NNNpx`` / ``w:NN%`` — explicit width clamp. Only consulted when
      no ``h:`` is present; a width hint <50% is a weak proxy for "small
      image" and downgrades the cost to ``geo.image_small_units``. This is
      the legacy behaviour preserved verbatim.
    - **No keyword** — when the image file is locally resolvable relative to
      ``deck_path`` (issue #622), read its pixel dimensions and charge the
      *width-normalized rendered height* (``height × content_width / width``,
      converted to line units and capped at ``geo.image_units``). A
      wide-aspect PNG (e.g. a 3096×684 mermaid flow chart) renders far
      shorter than the flat full-width assumption, so the flat 7.0u fallback
      over-fired on keyword-less decks. When the path is not resolvable
      (``deck_path=None``, a URL, a missing file, a non-PNG, or a parse
      error) the charge gracefully falls back to ``geo.image_units`` — the
      full-width assumption, unchanged for unannotated standalone-image
      blocks.

    Issue #562 / canary friction: the GoodBoy deck used ``![bg right:55%]``
    hero panels and ``![h:230px]`` clamped figures heavily. The pre-#562
    capacity model charged ``geo.image_units = 7.0u`` for both, blowing the
    13u budget by ~5u on slides that the rendered PDF showed sitting
    comfortably inside the safe area. The reviewer was forced to
    hand-confirm against the PDF on every pass — defeating the
    deterministic gate. Recognising ``bg`` (zero cost) and ``h:`` (true
    vertical cost) brings the source-side estimate into agreement with
    what the renderer actually produces.
    """
    if not alt_text:
        # No alt-string at all — no keywords possible. Still attempt the
        # aspect-aware refinement (issue #622): ``![](wide.png)`` is exactly
        # the keyword-less default-drafter shape that over-fired the flat
        # charge on wide-aspect PNGs.
        return _keywordless_image_cost(geo, image_path, deck_path)

    # Pad the alt-string with leading/trailing whitespace so the keyword
    # regexes (which use ``(?:^|\s)`` anchors to enforce token boundaries)
    # match keywords at either edge.
    padded = f" {alt_text} "

    # `bg` keyword: any form. Background images do not consume body flow.
    if _IMAGE_BG_KEYWORD_RE.search(padded):
        return (0.0, "image-background")

    # `h:` keyword (explicit vertical clamp). This is the most direct
    # signal of vertical body-flow cost; prefer it over `w:` when both are
    # present.
    m_h = _IMAGE_HEIGHT_KEYWORD_RE.search(padded)
    if m_h:
        h = m_h.group("height")
        try:
            if h.endswith("px"):
                px = int(h[:-2])
                # 1 line unit = body_line_height_px; convert px → units.
                units = max(0.5, px / float(geo.body_line_height_px))
                return (units, f"image(h:{h})")
            if h.endswith("%"):
                pct = int(h[:-1])
                units = max(0.5, (pct / 100.0) * geo.capacity_units)
                return (units, f"image(h:{h})")
        except ValueError:
            pass

    # `w:` keyword fallback (width as a weak proxy for "is this small?").
    m_w = _IMAGE_WIDTH_KEYWORD_RE.search(padded)
    if m_w:
        w = m_w.group("width")
        try:
            if w.endswith("%"):
                pct = int(w[:-1])
                if pct < 50:
                    return (geo.image_small_units, "image-small")
            elif w.endswith("px"):
                px = int(w[:-2])
                if px < (geo.slide_width_px // 2):
                    return (geo.image_small_units, "image-small")
        except ValueError:
            pass

    # No size keyword and no `bg` keyword: fall through to the aspect-aware
    # refinement (or the flat full-width assumption).
    return _keywordless_image_cost(geo, image_path, deck_path)


def _keywordless_image_cost(
    geo: Geometry, image_path: str | None, deck_path: Path | None
) -> tuple[float, str]:
    """Cost of a standalone image that carries no Marp sizing keyword.

    Before falling back to the flat full-width assumption
    (``geo.image_units``), try to refine the charge using the image's actual
    pixel aspect ratio (issue #622): a wide-aspect PNG rendered to the
    content width is much shorter than a square one, so the flat 7.0u charge
    over-fired on keyword-less decks. Only attempted when the image is a
    locally-resolvable PNG relative to ``deck_path``; any failure (no path,
    URL, missing file, non-PNG, parse error, zero dimension) falls through to
    the legacy flat charge.
    """
    if image_path and deck_path is not None:
        dims = _resolve_image_dimensions(image_path, deck_path)
        if dims is not None:
            width_px, height_px = dims
            if width_px > 0 and height_px > 0:
                # The deck CSS uses the same padding on all four sides, so the
                # top/bottom padding constant doubles as the left/right value
                # for the effective content width.
                content_width_px = (
                    geo.slide_width_px
                    - geo.top_padding_px
                    - geo.bottom_padding_px
                )
                rendered_height_px = height_px * (content_width_px / width_px)
                units = rendered_height_px / float(geo.body_line_height_px)
                units = min(geo.image_units, max(0.5, units))
                return (units, f"image({width_px}x{height_px})")

    # Full-width assumption (path not resolvable or refinement unavailable).
    return (geo.image_units, "image")


def _estimate_slide_cost(
    slide: _Slide,
    geo: Geometry,
    *,
    flex_class_names: frozenset[str] = frozenset(),
    deck_path: Path | None = None,
) -> _CostBreakdown:
    """Estimate the slide's vertical-line-unit cost from its markdown source."""
    return _accumulate_line_costs(
        slide.body.splitlines(),
        geo,
        flex_class_names=flex_class_names,
        deck_path=deck_path,
    )


def _accumulate_line_costs(
    lines: list[str],
    geo: Geometry,
    *,
    flex_class_names: frozenset[str] = frozenset(),
    deck_path: Path | None = None,
) -> _CostBreakdown:
    """Accumulate the vertical-line-unit cost of a run of markdown lines.

    Split out from ``_estimate_slide_cost`` (issue #622) so a flex/grid
    container's children can be re-costed recursively: the container's inner
    lines are estimated with the same model, then the accumulated total is
    scaled by ``geo.flex_container_cost_factor`` to reflect side-by-side
    (rather than stacked) rendering.
    """
    breakdown = _CostBreakdown()
    i = 0
    n = len(lines)
    in_fence = False
    fence_open_line = ""
    just_added_paragraph_break = False
    seen_first_block = False

    while i < n:
        raw_line = lines[i]
        stripped = raw_line.strip()

        # Skip directive comments (and the lint-disable comment).
        if _DIRECTIVE_COMMENT_RE.match(raw_line):
            i += 1
            continue

        # Flex/grid container (issue #622): a `<div class="X">` where X (or
        # one of its space-separated classes) is defined `display:flex|grid`
        # in the frontmatter `style:` block renders its children side-by-side.
        # Accumulate the inner lines' cost recursively and charge only
        # `flex_container_cost_factor` of it (the columns share vertical
        # extent rather than stacking). The opening and closing `<div>`/
        # `</div>` tag lines are consumed here so they are not later
        # mis-charged as body paragraphs.
        if flex_class_names and not in_fence:
            m_div = _DIV_CLASS_OPEN_RE.search(raw_line)
            if m_div and (set(m_div.group(1).split()) & flex_class_names):
                # Walk forward to the matching `</div>`, tracking nesting
                # depth. If no close is found, the container runs to the end
                # of the slide (safe approximation for Marp's HTML handling).
                depth = 1
                j = i + 1
                inner_lines: list[str] = []
                while j < n:
                    line_j = lines[j]
                    depth += len(_DIV_OPEN_TOKEN_RE.findall(line_j))
                    depth -= len(_DIV_CLOSE_TOKEN_RE.findall(line_j))
                    if depth <= 0:
                        break  # this line closes our container
                    inner_lines.append(line_j)
                    j += 1
                sub = _accumulate_line_costs(
                    inner_lines,
                    geo,
                    flex_class_names=flex_class_names,
                    deck_path=deck_path,
                )
                breakdown.add(
                    "flex-container",
                    sub.total_units * geo.flex_container_cost_factor,
                )
                i = j + 1
                seen_first_block = True
                just_added_paragraph_break = False
                continue

        # Track fenced code blocks (don't try to interpret their contents).
        if not in_fence and _FENCED_OPEN_RE.match(raw_line):
            in_fence = True
            fence_open_line = raw_line.strip()[:3]
            j = i + 1
            code_lines = 0
            while j < n:
                if lines[j].strip().startswith(fence_open_line):
                    break
                code_lines += 1
                j += 1
            breakdown.add(
                f"code-block({code_lines} lines)",
                geo.code_block_overhead_units + code_lines * geo.code_line_units,
            )
            i = j + 1
            in_fence = False
            seen_first_block = True
            just_added_paragraph_break = False
            continue

        # Blank line: paragraph break (small cost between adjacent blocks).
        if not stripped:
            if seen_first_block and not just_added_paragraph_break:
                breakdown.add("paragraph-break", geo.paragraph_break_units)
                just_added_paragraph_break = True
            i += 1
            continue

        # Heading.
        m_heading = _HEADING_RE.match(raw_line)
        if m_heading:
            level = len(m_heading.group(1))
            cost = (
                geo.h1_units
                if level == 1
                else geo.h2_units
                if level == 2
                else geo.h3_units
                if level == 3
                else geo.h4_plus_units
            )
            breakdown.add(f"h{level}", cost)
            breakdown.heading_levels.append(level)
            i += 1
            seen_first_block = True
            just_added_paragraph_break = False
            continue

        # Horizontal rule inside a slide.
        if _HR_RE.match(raw_line):
            breakdown.add("hr", geo.hr_inside_slide_units)
            i += 1
            seen_first_block = True
            just_added_paragraph_break = False
            continue

        # Blockquote (single-line).
        if _BLOCKQUOTE_RE.match(raw_line):
            breakdown.add("blockquote", geo.blockquote_units)
            i += 1
            seen_first_block = True
            just_added_paragraph_break = False
            continue

        # Tables.
        if _TABLE_ROW_RE.match(raw_line):
            # consume table block
            row_count = 0
            j = i
            saw_separator = False
            while j < n and _TABLE_ROW_RE.match(lines[j]):
                if _TABLE_SEP_RE.match(lines[j]):
                    saw_separator = True
                else:
                    row_count += 1
                j += 1
            if saw_separator and row_count >= 1:
                # one header + (row_count - 1) body rows
                breakdown.add(
                    f"table({row_count} rows)",
                    geo.table_header_units + max(0, row_count - 1) * geo.table_row_units,
                )
            else:
                breakdown.add(
                    f"table-like({row_count})",
                    row_count * geo.table_row_units,
                )
            i = j
            seen_first_block = True
            just_added_paragraph_break = False
            continue

        # Bullet.
        m_bullet = _BULLET_RE.match(raw_line)
        if m_bullet:
            indent = len(m_bullet.group(1))
            text = m_bullet.group(3)
            unit = geo.bullet_units if indent < 2 else geo.nested_bullet_units
            # Account for wrap.
            wraps = max(0, (len(text) - 1) // geo.bullet_chars_per_line)
            breakdown.add(
                f"bullet({len(text)}c{'+wrap' if wraps else ''})",
                unit + wraps * geo.bullet_continuation_units,
            )
            i += 1
            seen_first_block = True
            just_added_paragraph_break = False
            continue

        # Image (standalone block — image on its own paragraph). Keyed on
        # line *structure* (the whole line is exactly one image node), not
        # on line length — a long alt string must not push a standalone
        # image into the body-paragraph branch below (#905).
        if _STANDALONE_FIGURE_RE.match(raw_line):
            # Parse the alt-string for Marp sizing keywords (`bg`, `h:N`,
            # `w:N`, …). `_image_cost_units` returns the vertical body-flow
            # cost; see its docstring for the keyword→cost mapping.
            # Background images consume 0u; explicit-height images
            # translate `h:` directly to line units; everything else falls
            # back to the legacy width-only heuristic. Issue #562.
            m_alt = _IMAGE_ALT_RE.search(raw_line)
            alt = m_alt.group("alt") if m_alt else ""
            m_path = _IMAGE_RE.search(raw_line)
            img_path = m_path.group(1) if m_path else None
            units, label = _image_cost_units(
                alt, geo, image_path=img_path, deck_path=deck_path
            )
            breakdown.add(label, units)
            i += 1
            seen_first_block = True
            just_added_paragraph_break = False
            continue

        # Body paragraph — accumulate consecutive non-block lines.
        para_lines: list[str] = []
        while i < n:
            line = lines[i]
            stripped_line = line.strip()
            if not stripped_line:
                break
            if (
                _HEADING_RE.match(line)
                or _BULLET_RE.match(line)
                or _HR_RE.match(line)
                or _BLOCKQUOTE_RE.match(line)
                or _TABLE_ROW_RE.match(line)
                or _FENCED_OPEN_RE.match(line)
                or _DIRECTIVE_COMMENT_RE.match(line)
            ):
                break
            # Standalone image line was handled above; mixed-text-with-image
            # paragraphs count as paragraph + image.
            para_lines.append(line)
            i += 1
        if para_lines:
            joined = " ".join(s.strip() for s in para_lines)
            chars = len(joined)
            wraps = max(
                0, (chars - 1) // geo.body_paragraph_chars_per_line
            )
            inline_image = bool(_IMAGE_RE.search(joined))
            cost = geo.body_paragraph_units + wraps * geo.extra_body_wrap_units
            if inline_image:
                cost += geo.image_small_units
                breakdown.add(
                    f"paragraph({chars}c+inline-image)",
                    cost,
                )
            else:
                breakdown.add(f"paragraph({chars}c)", cost)
            seen_first_block = True
            just_added_paragraph_break = False
            continue

        # Fallback: count as one body line.
        breakdown.add("misc", 1.0)
        i += 1
        seen_first_block = True
        just_added_paragraph_break = False

    return breakdown


# figure-italic-supporting-line-too-long check --------------------------------


def _check_italic_supporting_lines(
    slide: _Slide, geo: Geometry, suppressed: bool
) -> list[Finding]:
    """Detect long italic supporting lines directly under a standalone figure.

    Implements the rule documented in the module docstring's "Anvil-specific
    scope" section. State machine, per slide:

    1. Scan ``slide.body`` lines. Skip blank and directive-comment lines.
    2. **Trigger**: a line matching ``_STANDALONE_FIGURE_RE`` (a single
       ``![alt](path)`` reference that IS the line, modulo whitespace).
    3. **Advance** past blank and directive-comment lines.
    4. **Italic accumulator**: if the next non-blank, non-directive line
       matches ``_FULL_LINE_ITALIC_RE`` (single ``_..._`` or ``*...*``
       spanning the whole stripped line, bold-italic explicitly rejected),
       enter italic-block state. Continue accumulating consecutive italic
       lines (soft-wrap support) until a blank, non-italic, directive, or
       end-of-slide closes the block.
    5. **Measure**: word count = ``len(inner.split())``; char count =
       ``len(inner)`` of the inner text with the italic delimiters stripped
       (delimiters don't render and shouldn't be counted).
    6. **Flag** if ``words > geo.italic_supporting_line_max_words`` OR
       ``chars > geo.italic_supporting_line_max_chars``. Emit a ``warning``
       with ``rule="figure-italic-supporting-line-too-long"`` (downgraded
       to ``info`` if the per-slide ``anvil-lint-disable`` directive is set
       for this rule).
    7. After any close (flagged or not), continue scanning for the next
       figure trigger within the same slide. A slide with two figures gets
       two independent checks.
    """
    findings: list[Finding] = []
    body_lines = slide.body.splitlines()
    n = len(body_lines)
    i = 0

    while i < n:
        line = body_lines[i]
        stripped = line.strip()

        # Skip blanks and directive comments while hunting for a trigger.
        if not stripped or _DIRECTIVE_COMMENT_RE.match(line):
            i += 1
            continue

        # Look for the trigger: a standalone figure block.
        if not _STANDALONE_FIGURE_RE.match(line):
            i += 1
            continue

        # Trigger found. Advance past blanks and directive lines.
        j = i + 1
        while j < n:
            stripped_j = body_lines[j].strip()
            if not stripped_j or _DIRECTIVE_COMMENT_RE.match(body_lines[j]):
                j += 1
                continue
            break

        # j is now at the next non-blank, non-directive line (or past end).
        if j >= n:
            break

        # Is it an italic line? If not, no italic-block to measure — go back
        # to scanning for the next trigger from the next line.
        first_italic_match = _FULL_LINE_ITALIC_RE.match(body_lines[j])
        if not first_italic_match:
            i = j + 1
            continue

        # Italic accumulator: consume consecutive italic lines (soft-wrap)
        # until a blank, non-italic, directive, or end-of-slide.
        block_start = j
        inner_parts: list[str] = [first_italic_match.group(1).strip()]
        k = j + 1
        while k < n:
            line_k = body_lines[k]
            stripped_k = line_k.strip()
            if not stripped_k:
                break
            if _DIRECTIVE_COMMENT_RE.match(line_k):
                break
            m_k = _FULL_LINE_ITALIC_RE.match(line_k)
            if not m_k:
                break
            inner_parts.append(m_k.group(1).strip())
            k += 1

        # Measure across the accumulated block. Delimiters are excluded
        # because they don't render.
        inner_text = " ".join(p for p in inner_parts if p)
        words = len(inner_text.split())
        chars = len(inner_text)

        over_words = words > geo.italic_supporting_line_max_words
        over_chars = chars > geo.italic_supporting_line_max_chars
        if over_words or over_chars:
            # Compose the message (per AC1 / the curator's example phrasing).
            message = (
                f"Italic supporting line under figure is {words} words / "
                f"{chars} chars; budget is "
                f"≤{geo.italic_supporting_line_max_words} words / "
                f"≤{geo.italic_supporting_line_max_chars} chars. "
                "Likely wraps to 2+ lines and clips at slide bottom on 16:9 "
                "(italic glyphs run ~5% wider than upright body weight)."
            )
            findings.append(
                Finding(
                    slide=slide.index,
                    # 1-based file-level line, computed via the same
                    # convention as slide-content-overflow: slide.start_line
                    # is the 1-based first-line of the slide; block_start is
                    # the 0-based offset within slide.body of the italic
                    # block's first line.
                    line=slide.start_line + block_start,
                    rule="figure-italic-supporting-line-too-long",
                    severity="info" if suppressed else "warning",
                    message=message,
                )
            )

        # Continue scanning from the line after the italic block — a slide
        # with two figures gets two independent checks.
        i = k
        continue

    return findings


# inline-display-style-dropped check ------------------------------------------


def _check_inline_display_styles(
    slide: _Slide, suppressed: bool
) -> list[Finding]:
    """Detect inline ``style="...display:(grid|flex|...)..."`` attributes.

    Marp renders slide content into a ``<foreignObject>`` element inside an
    SVG and rasterizes via Chromium for ``--pdf`` output. Inline
    ``display: grid`` / ``display: flex`` rules are silently dropped through
    that path — the slide compiles cleanly but the layout flattens to a
    single column in the rendered PDF (verified, issue #128). The reliable
    workaround is a frontmatter ``style: |`` block defining a CSS class,
    referenced from ``<div class="...">`` in the slide body.

    The check is a simple regex scan over the slide body line-by-line; one
    finding is emitted per matching line. Fenced code blocks are excluded
    (a ``style="display:grid"`` inside a markdown code fence is documentation,
    not a render bug).

    Suppressed findings downgrade to ``info`` (same protocol as the other
    Anvil-original rules).
    """
    findings: list[Finding] = []
    body_lines = slide.body.splitlines()
    n = len(body_lines)
    i = 0
    in_fence = False
    fence_open_line = ""

    while i < n:
        line = body_lines[i]
        stripped = line.strip()

        # Track fenced code blocks (don't flag inline styles inside them).
        if not in_fence and _FENCED_OPEN_RE.match(line):
            in_fence = True
            fence_open_line = stripped[:3]
            i += 1
            continue
        if in_fence:
            if stripped.startswith(fence_open_line):
                in_fence = False
            i += 1
            continue

        # Try double-quoted then single-quoted.
        m = _INLINE_DISPLAY_STYLE_DQ_RE.search(line)
        if not m:
            m = _INLINE_DISPLAY_STYLE_SQ_RE.search(line)
        if m:
            value = m.group("value").lower()
            message = (
                f"Inline `style=\"...display:{value}...\"` is silently "
                "dropped by Marp's foreignObject SVG render path — the "
                "slide will compile cleanly but flatten to single-column "
                "stacked output in the PDF (issue #128). Move the rule "
                "into the deck frontmatter `style: |` block as a CSS class "
                "and apply it via `<div class=\"...\">`; class-based "
                "selectors are honored through the foreignObject path. "
                "See `marp-renderer.md` \"Layout patterns\" for the "
                "worked example."
            )
            findings.append(
                Finding(
                    slide=slide.index,
                    line=slide.start_line + i,
                    rule="inline-display-style-dropped",
                    severity="info" if suppressed else "warning",
                    message=message,
                )
            )
        i += 1

    return findings


# Public API -------------------------------------------------------------------


def lint_source(
    source: str,
    *,
    geometry: Geometry | None = None,
    rules: tuple[str, ...] = PORTED_RULES,
    deck_path: Path | None = None,
) -> LintResult:
    """Run the lint over an in-memory Marp markdown source string.

    This is the unit-testable core; ``lint_deck`` is a thin file wrapper.

    ``deck_path`` (issue #622), when provided, is the on-disk location of the
    source file. It lets the ``slide-content-overflow`` capacity model resolve
    keyword-less image references relative to the deck and charge their true
    (width-normalized) rendered height instead of the flat full-width
    assumption. Passing ``None`` (the default, and the in-memory call path)
    preserves the pre-#622 behavior exactly.
    """
    geo = geometry or _DEFAULT_GEOMETRY
    result = LintResult()
    run_overflow = "slide-content-overflow" in rules
    run_italic = "figure-italic-supporting-line-too-long" in rules
    run_inline_display = "inline-display-style-dropped" in rules
    if not (run_overflow or run_italic or run_inline_display):
        return result

    # Deck-wide frontmatter CSS flex/grid class names (issue #622), parsed
    # once. Empty frozenset when there is no frontmatter `style:` block or no
    # flex/grid class — in which case the flex-container cost path is inert.
    flex_class_names = _collect_flex_class_names(source)

    slides = _split_slides(source)
    for slide in slides:
        # Escape hatch — collected once per slide; each rule asks the set.
        disabled_rules = _collect_disabled_rules(slide.raw)

        # --- figure-italic-supporting-line-too-long ----------------------
        # Run this first because it does not depend on the capacity model.
        # Suppressed findings downgrade to ``info`` (same protocol as the
        # overflow rule's escape hatch).
        if run_italic:
            italic_suppressed = (
                "figure-italic-supporting-line-too-long" in disabled_rules
            )
            for finding in _check_italic_supporting_lines(
                slide, geo, italic_suppressed
            ):
                if finding.severity == "info":
                    result.infos.append(finding)
                else:
                    result.warnings.append(finding)

        # --- inline-display-style-dropped --------------------------------
        # Pure regex scan; independent of the capacity model. Suppressed
        # findings downgrade to ``info``.
        if run_inline_display:
            inline_suppressed = (
                "inline-display-style-dropped" in disabled_rules
            )
            for finding in _check_inline_display_styles(slide, inline_suppressed):
                if finding.severity == "info":
                    result.infos.append(finding)
                else:
                    result.warnings.append(finding)

        if not run_overflow:
            continue

        suppressed = "slide-content-overflow" in disabled_rules

        breakdown = _estimate_slide_cost(
            slide, geo, flex_class_names=flex_class_names, deck_path=deck_path
        )

        # Anti-pattern penalty: H1 + H2 on the same slide (#25 repro).
        heading_set = set(breakdown.heading_levels)
        if 1 in heading_set and 2 in heading_set:
            breakdown.add("h1+h2-anti-pattern", geo.h1_plus_h2_penalty_units)

        # `_class: ask` capacity reduction (heavier padding per anvil-deck.css).
        slide_capacity = geo.capacity_units
        is_ask_slide = bool(_CLASS_ASK_RE.search(slide.raw))
        if is_ask_slide:
            slide_capacity -= geo.ask_class_capacity_penalty_units

        overage = breakdown.total_units - slide_capacity

        if overage <= geo.warning_threshold_units:
            continue

        # Build a human-readable message.
        top_costs = sorted(breakdown.parts, key=lambda p: -p[1])[:3]
        cost_summary = ", ".join(f"{label}={units:.1f}u" for label, units in top_costs)
        capacity_note = (
            f" (ask-slide capacity {slide_capacity:.1f}u)"
            if is_ask_slide
            else ""
        )
        message = (
            f"Slide exceeds estimated vertical capacity by "
            f"~{overage:.1f} line-units "
            f"(estimated {breakdown.total_units:.1f}u vs. capacity {slide_capacity:.1f}u). "
            f"Top costs: {cost_summary}.{capacity_note}"
        )

        finding = Finding(
            slide=slide.index,
            line=slide.start_line,
            rule="slide-content-overflow",
            severity="info" if suppressed else (
                "error" if overage >= geo.error_threshold_units else "warning"
            ),
            message=message,
        )
        if suppressed:
            result.infos.append(finding)
        elif finding.severity == "error":
            result.errors.append(finding)
        else:
            result.warnings.append(finding)

    return result


def _collect_disabled_rules(slide_src: str) -> set[str]:
    rules: set[str] = set()
    for m in _LINT_DISABLE_RE.finditer(slide_src):
        for raw in m.group("rules").split(","):
            r = raw.strip()
            if r:
                rules.add(r)
    return rules


def lint_deck(path: Path, *, geometry: Geometry | None = None) -> LintResult:
    """Run the lint against a Marp ``deck.md`` file on disk.

    Per AC1 on issue #31. Pass a custom ``geometry`` to override the default
    16:9 / 1280×720 / anvil-deck.css constants.
    """
    if not isinstance(path, Path):
        path = Path(path)
    source = path.read_text(encoding="utf-8")
    return lint_source(source, geometry=geometry, deck_path=path)


__all__ = [
    "Finding",
    "Geometry",
    "LintResult",
    "PORTED_RULES",
    "ThemeCapacityContract",
    "UPSTREAM_SHA",
    "geometry_from_theme_contract",
    "geometry_from_theme_css",
    "lint_deck",
    "lint_source",
]
