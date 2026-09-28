"""Figure-content VLM critic (Epic #328 Phase 4, issue #340).

This module ships the **figure-content** VLM critic — a vision-language-model
pass that scores every figure in a memo or report version directory along
three axes:

1. **On-brand match** against ``anvil/lib/figures/palette.py`` (does the
   figure use the Anvil navy / muted-grey ramp, or has it slipped into
   matplotlib default tab10 / a non-brand accent?).
2. **Caption-claim grounding** (does the caption accurately describe what
   the figure visually depicts?).
3. **Adjacency-claim grounding** (does the figure support the surrounding
   prose claim, or is it a non-sequitur next to the text that introduces
   it?).

Direct-lib placement (NOT skill-local)
--------------------------------------

This critic ships at ``anvil/lib/figure_content.py`` (not under
``anvil/skills/memo/lib/`` like the Phase 2 ``hyperlink_resolver`` precedent)
because two consumers — the ``memo`` skill and the ``report`` skill — both
have figure-evidence dimensions today and reach for this primitive
simultaneously. The CLAUDE.md ``Skill-local first, lib promotion later``
rule explicitly carves out the two-consumer threshold: the rule is "wait
for the *second* consumer before generalizing", which is satisfied at ship.

Design contract (settled at Epic #328 reactivation; do NOT re-litigate)
-----------------------------------------------------------------------

- **No schema delta.** Every emitted ``Finding`` uses the existing free-form
  ``Finding.suggested_fix`` text. No ``action`` / ``target_anchor`` /
  ``proposed_content`` fields. Matches the Phase 2 (hyperlink-resolver,
  #335 / PR #338) and Phase 3 (citation-coverage, #336 / PR #337) settle.
- **VLM cost cap.** Per-figure budget enforced at module level. The default
  is **one** VLM call per figure per run; pass ``vlm_budget_per_figure=N``
  to ``critique_version_dir`` to tune.
- **Content-hash cache.** A session-lifetime in-process cache keyed by the
  SHA-256 of the figure bytes prevents the same image from being VLM-passed
  twice within a single run. The cache is intentionally **internal** to
  this module; promotion to ``anvil/lib/vision_cache.py`` is a follow-on
  if Phase 5 (``image-accessibility``, #341) reaches for the same shape.
- **Critical flag.** ``critical_figure_misrepresents_claim`` fires when
  the VLM detects a caption-vs-figure contradiction (e.g. caption says
  "revenue tripled in Q3" but the figure shows a flat line). The aggregator's
  ``compute_verdict`` short-circuits to ``Verdict.BLOCK`` per the issue
  #340 AC.
- **Subprocess-only for figure extraction.** PDF-to-PNG uses ``pdftoppm``
  (poppler-utils) via ``anvil.lib.render.render_pdf_to_pngs``. When
  ``pdftoppm`` is not on PATH the critic graceful-degrades: it emits a
  top-level ``reason`` and zero findings (no false-positive findings on a
  pipeline missing the tool).

Two figure discovery paths
--------------------------

1. **Rendered PDF**: when ``<version_dir>/<slug>.pdf`` (memo / report
   convention) exists, each page is extracted as a PNG via ``pdftoppm``
   into a temporary directory and treated as one figure.
2. **Direct sources**: ``<version_dir>/figures/`` (any depth) is walked for
   ``.png`` / ``.jpg`` / ``.jpeg`` / ``.svg`` files. SVG files are skipped
   (the VLM consumes raster images; an SVG figure is recorded as
   "unverified" via a top-level reason rather than a finding so the operator
   sees the gap without a false positive).

The two paths are **complementary**: a memo that has both a draft PDF and
a ``figures/`` source dir gets both surfaces critiqued. The hash cache
deduplicates if the rendered page and the source PNG share bytes (rare
in practice — pdftoppm rasterizes at a fixed DPI; the source PNG was
typically authored at a different one).

CLI entry-point
---------------

::

    python -m anvil.lib.figure_content <version_dir> [--write-review]

Exit codes mirror the Phase 2 / Phase 3 precedents:

- ``0``: clean pass (no findings, no critical flag).
- ``1``: one or more findings (or a critical flag).
- ``2``: invocation error (missing ``version_dir``).

Coordination with sibling deferred phases
-----------------------------------------

#341 (``image-accessibility``) also touches VLM and may benefit from the
content-hash cache. The cache is shipped **inline** here per the issue
body's coordination note; promotion to a shared ``anvil/lib/vision_cache.py``
is deferred until #341's builder reaches for the same shape.

#342 (``claim-figure-grounding``) shares figure-discovery logic (walking
``figures/`` and the PDF). Same deferral: ship inline; promote later if
duplication is observed.

All three deferred-phase critics share the CLI shape
``python -m <module> <version_dir> [--write-review]`` and the
``<version_dir>.<tag>/`` sibling-dir convention so the
``anvil/lib/critics.py::discover_critics`` auto-discovery contract picks
up the result without aggregator changes.
"""

from __future__ import annotations

import hashlib
import json
import shutil
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence

from anvil.lib.figures.palette import (
    ANVIL_BG,
    ANVIL_BG_SECTION,
    ANVIL_INK,
    ANVIL_MUTED,
    ANVIL_NAVY,
    ANVIL_NAVY_TINT,
    ANVIL_RULE,
    ANVIL_SUCCESS,
    ANVIL_WARNING,
)
from anvil.lib.review_schema import (
    CriticalFlag,
    Finding,
    Kind,
    Review,
    Score,
)
from anvil.lib.sidecar import write_critic_review_dir
from anvil.lib.vision import (
    VisionCallback,
    VisionCritic,
    VisionDimension,
    VisionRubric,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------


CRITIC_ID = "figure-content"
"""Stable critic identifier surfaced on ``_review.json.critic_id``."""

SIBLING_SUFFIX = "figure-content"
"""Trailing tag for the sibling critic dir: ``<version_dir>.figure-content/``."""

RUBRIC_ID = "anvil-figure-content-v1"
"""Pinned rubric id surfaced on ``_review.json.rubric``."""


# Critical-flag taxonomy. The single critical flag this critic raises.
CRITICAL_FIGURE_MISREPRESENTS_CLAIM = "critical_figure_misrepresents_claim"
"""Raised by the VLM when caption text contradicts the figure's depiction
(e.g. caption claims a 3x increase, figure shows a flat line). Aggregator's
``compute_verdict`` short-circuits to ``Verdict.BLOCK``."""


# Scoring axes (three per figure, each /5).
DIM_ON_BRAND = "on_brand"
DIM_CAPTION_GROUNDING = "caption_grounding"
DIM_ADJACENCY_GROUNDING = "adjacency_grounding"


# VLM budget default. Conservative: one VLM call per figure per run.
DEFAULT_VLM_BUDGET_PER_FIGURE = 1


# Recognized raster extensions for direct-source discovery. SVG is excluded
# from VLM probing (vector format; the VLM contract is raster bytes); we
# surface SVG presence via a top-level reason instead of a false-positive
# finding.
_RASTER_EXTS = frozenset({".png", ".jpg", ".jpeg", ".webp", ".gif"})
_SVG_EXT = ".svg"


# Canonical brand palette as a frozen set of lowercased hex strings. The VLM
# is told this set explicitly in the prompt so it scores ``on_brand`` against
# the documented palette (not its prior on "what looks like a corporate brand").
_BRAND_PALETTE_HEX: Sequence[str] = (
    ANVIL_NAVY,
    ANVIL_INK,
    ANVIL_MUTED,
    ANVIL_NAVY_TINT,
    ANVIL_RULE,
    ANVIL_BG,
    ANVIL_BG_SECTION,
    ANVIL_WARNING,
    ANVIL_SUCCESS,
)


# ---------------------------------------------------------------------------
# Rubric — three axes per figure
# ---------------------------------------------------------------------------


def default_figure_content_rubric() -> VisionRubric:
    """Return the three-axis figure-content rubric (each /5, max_total=15).

    The dimensions are the three scoring axes from the #340 issue body:

    - ``on_brand`` — palette match against ``anvil/lib/figures/palette.py``.
      0 = matplotlib default tab10 or off-brand crimson/teal/etc. dominates
      the figure; 5 = navy-anchored, in-palette throughout.
    - ``caption_grounding`` — caption accuracy. 0 = caption claims something
      the figure does not show; 5 = caption is a fair, specific description
      of the figure's actual content.
    - ``adjacency_grounding`` — does the figure support the surrounding
      prose? 0 = non-sequitur; the prose claim is unsupported by the figure;
      5 = the figure clearly advances or evidences the adjacent claim.

    The rubric is composed via :class:`VisionRubric` (the shared substrate)
    so the existing ``VisionCritic`` machinery (prompt building, payload →
    Review mapping, score clamping) works without changes.
    """
    return VisionRubric(
        dimensions=(
            VisionDimension(
                name=DIM_ON_BRAND,
                max=5,
                description=(
                    "Does the figure use the Anvil brand palette "
                    "(navy / muted grey / navy tint / rule grey; see "
                    "anvil/lib/figures/palette.py)? 5 = palette-aligned; "
                    "0 = matplotlib default tab10 dominates, or an off-brand "
                    "accent (crimson, teal, magenta, gold) is used as a "
                    "primary series color."
                ),
            ),
            VisionDimension(
                name=DIM_CAPTION_GROUNDING,
                max=5,
                description=(
                    "Does the caption accurately describe what the figure "
                    "depicts? 5 = caption is a fair, specific description "
                    "of the figure's actual content; 0 = caption claims "
                    "something the figure does not show (the load-bearing "
                    "contradiction case)."
                ),
            ),
            VisionDimension(
                name=DIM_ADJACENCY_GROUNDING,
                max=5,
                description=(
                    "Does the figure support the surrounding prose claim? "
                    "5 = the figure clearly advances or evidences the "
                    "adjacent claim; 0 = the figure is a non-sequitur next "
                    "to the prose that introduces it (drop or replace)."
                ),
            ),
        ),
        rubric_id=RUBRIC_ID,
    )


# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FigureRecord:
    """One discovered figure plus its provenance.

    Attributes
    ----------
    path
        Absolute path to the figure file (PNG / JPG / SVG / extracted page).
    source
        Provenance tag: ``"pdf-page"`` (extracted from the rendered PDF via
        ``pdftoppm``) or ``"figures-dir"`` (direct raster source).
    label
        Short human-readable label used in evidence spans, e.g.
        ``"page-3"`` or ``"figures/hero-chart.png"``.
    content_hash
        SHA-256 of the figure bytes. The cache key.
    """

    path: Path
    source: str
    label: str
    content_hash: str


@dataclass
class FigureContentResult:
    """Outcome of one ``critique_version_dir`` pass.

    Mirrors :class:`hyperlink_resolver.HyperlinkResolverResult` and
    :class:`render_gate.GateResult` shapes so downstream aggregation is
    uniform across the deterministic-checks + tool-evidence families.
    """

    version_dir: str
    rendered_artifact: str
    figures: List[FigureRecord] = field(default_factory=list)
    findings: List[Finding] = field(default_factory=list)
    critical_flags: List[CriticalFlag] = field(default_factory=list)
    reasons: List[str] = field(default_factory=list)
    scores: List[Score] = field(default_factory=list)
    vlm_calls: int = 0
    cache_hits: int = 0

    def passed(self) -> bool:
        """``True`` when no findings and no critical flags."""
        return not self.findings and not self.critical_flags

    def to_json(self) -> dict:
        """JSON-serializable summary mirroring the Phase 2 / Phase 3 shape."""
        return {
            "critic": CRITIC_ID,
            "version_dir": self.version_dir,
            "rendered_artifact": self.rendered_artifact,
            "figures": [
                {
                    "label": fr.label,
                    "source": fr.source,
                    "path": str(fr.path),
                    "content_hash": fr.content_hash,
                }
                for fr in self.figures
            ],
            "findings": [
                {
                    "severity": f.severity,
                    "dimension": f.dimension,
                    "rationale": f.rationale,
                    "suggested_fix": f.suggested_fix,
                    "evidence_span": f.evidence_span,
                }
                for f in self.findings
            ],
            "critical_flags": [
                {
                    "type": cf.type,
                    "justification": cf.justification,
                    "evidence_span": cf.evidence_span,
                }
                for cf in self.critical_flags
            ],
            "reasons": list(self.reasons),
            "vlm_calls": self.vlm_calls,
            "cache_hits": self.cache_hits,
            "pass": self.passed(),
        }

    def to_review(
        self,
        *,
        version_dir: Optional[str] = None,
        critic_id: str = CRITIC_ID,
        model: Optional[str] = None,
    ) -> Review:
        """Build a typed ``Review`` (``kind=Kind.VISION``).

        The review aggregates the per-figure scores into a single set of
        three rubric rows (``on_brand``, ``caption_grounding``,
        ``adjacency_grounding``) by taking the mean across figures (rounded
        to nearest int via round-half-to-even). When no figures were
        critiqued (e.g. empty version dir, or ``pdftoppm`` unavailable +
        no ``figures/`` dir), each row is null-scored.

        ``rendered_artifact`` is REQUIRED by the schema validator at
        ``review_schema.py:371`` when ``kind=Kind.VISION``; we set it to
        the path of the PDF or the ``figures/`` dir relative to the
        version dir, whichever was the primary source.
        """
        rubric = default_figure_content_rubric()
        # Aggregate per-figure scores into per-rubric-row averages.
        per_dim: Dict[str, List[int]] = {d.name: [] for d in rubric.dimensions}
        per_dim_critical: Dict[str, bool] = {
            d.name: False for d in rubric.dimensions
        }
        for s in self.scores:
            if s.dimension in per_dim and s.score is not None:
                per_dim[s.dimension].append(s.score)
            if s.dimension in per_dim_critical and s.critical:
                per_dim_critical[s.dimension] = True

        rolled_up_scores: List[Score] = []
        total = 0
        for dim in rubric.dimensions:
            values = per_dim[dim.name]
            if values:
                rolled = int(round(sum(values) / len(values)))
                total += rolled
            else:
                rolled = None
            rolled_up_scores.append(
                Score(
                    dimension=dim.name,
                    score=rolled,
                    max=dim.max,
                    critical=per_dim_critical[dim.name],
                    justification=(
                        f"Mean across {len(values)} figure(s)"
                        if values
                        else "no figures critiqued (see top-level reasons)"
                    ),
                )
            )

        return Review(
            schema_version="1",
            kind=Kind.VISION,
            version_dir=version_dir or self.version_dir,
            critic_id=critic_id,
            model=model,
            rubric=RUBRIC_ID,
            scores=rolled_up_scores,
            findings=list(self.findings),
            critical_flags=list(self.critical_flags),
            total=total,
            threshold=rubric.max_total(),
            rendered_artifact=self.rendered_artifact,
        )


# ---------------------------------------------------------------------------
# Tool availability (graceful-degrade preflight)
# ---------------------------------------------------------------------------


def check_pdftoppm_available() -> bool:
    """Return ``True`` when ``pdftoppm`` is on PATH.

    Mirrors the ``check_*_available`` family in :mod:`anvil.lib.render`
    (``check_mmdc_available``, ``check_pdfjam_available``, etc.) — a pure
    ``shutil.which`` guard so callers can preflight and pick a different
    path (or skip the PDF extraction entirely, falling back to direct
    ``figures/`` discovery) when the tool is missing.
    """
    return shutil.which("pdftoppm") is not None


# ---------------------------------------------------------------------------
# Figure discovery
# ---------------------------------------------------------------------------


def _hash_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _discover_pdf(version_dir: Path) -> Optional[Path]:
    """Return the rendered PDF for a memo or report version dir, or ``None``.

    Per the #295 model lock the body filename echoes the thread slug, and
    the render lands at ``<thread>.{N}/<thread>.pdf``. We accept that
    convention but also fall back to any single PDF in the version dir so
    a hand-rendered artifact (e.g. early-draft ``memo.pdf`` before the
    slug-echo rename) is still discoverable.
    """
    slug_pdf = version_dir / f"{version_dir.parent.name}.pdf"
    if slug_pdf.exists():
        return slug_pdf
    pdfs = sorted(version_dir.glob("*.pdf"))
    if len(pdfs) == 1:
        return pdfs[0]
    return None


def _discover_figures_dir_sources(version_dir: Path) -> List[Path]:
    """Walk ``<version_dir>/figures/`` for raster + SVG sources.

    Returns paths in sorted order (stable across runs). SVG files are
    returned alongside rasters; the caller emits a top-level reason for
    each SVG noting that the VLM does not consume vectors directly.
    """
    figures_dir = version_dir / "figures"
    if not figures_dir.is_dir():
        return []
    out: List[Path] = []
    for path in sorted(figures_dir.rglob("*")):
        if path.is_file() and path.suffix.lower() in _RASTER_EXTS | {_SVG_EXT}:
            out.append(path)
    return out


def discover_figures(
    version_dir: Path,
    *,
    pdf_dpi: int = 150,
    extract_dir: Optional[Path] = None,
) -> tuple[List[FigureRecord], str, List[str]]:
    """Walk a version dir for figures; return records + primary-source label.

    Two paths run in sequence:

    1. **PDF page extraction** — if a ``<slug>.pdf`` exists and
       ``pdftoppm`` is on PATH, each page is rasterized to a PNG (via
       :func:`anvil.lib.render.render_pdf_to_pngs`) in ``extract_dir``
       (a caller-provided tempdir; if ``None`` a tempdir is created and
       its path is stored as the parent of every extracted PNG).
    2. **figures/ dir walk** — every raster (and SVG, recorded as
       unverified) under ``<version_dir>/figures/`` is appended.

    Returns
    -------
    ``(records, rendered_artifact_label, reasons)``

    where ``rendered_artifact_label`` is the path (relative to
    ``version_dir.parent``) of the primary source — the PDF when present,
    else ``"figures/"`` when the figures-dir path produced records, else
    the version dir name itself (the schema requires the field to be
    set when ``kind=Kind.VISION``; we set a placeholder so the Review
    validates even on an empty critique).

    ``reasons`` carries graceful-degrade notes (``pdftoppm`` unavailable,
    SVG sources skipped, etc.) that the caller surfaces on
    :attr:`FigureContentResult.reasons`.
    """
    reasons: List[str] = []
    records: List[FigureRecord] = []

    pdf = _discover_pdf(version_dir)
    pdf_records: List[FigureRecord] = []
    if pdf is not None:
        if check_pdftoppm_available():
            from anvil.lib.render import render_pdf_to_pngs

            target_dir = extract_dir or Path(
                tempfile.mkdtemp(prefix="figure-content-")
            )
            try:
                page_pngs = render_pdf_to_pngs(
                    pdf, target_dir, dpi=pdf_dpi
                )
            except Exception as exc:
                reasons.append(
                    f"pdf extraction failed ({type(exc).__name__}: {exc}); "
                    f"falling back to figures/ dir discovery only."
                )
                page_pngs = []
            for page_png in page_pngs:
                data = page_png.read_bytes()
                pdf_records.append(
                    FigureRecord(
                        path=page_png,
                        source="pdf-page",
                        label=page_png.stem,
                        content_hash=_hash_bytes(data),
                    )
                )
        else:
            reasons.append(
                "pdftoppm not on PATH; PDF page extraction skipped "
                "(install poppler-utils to enable). figures/ dir "
                "discovery still runs."
            )
    records.extend(pdf_records)

    svg_skipped = 0
    figures_records: List[FigureRecord] = []
    for src in _discover_figures_dir_sources(version_dir):
        if src.suffix.lower() == _SVG_EXT:
            svg_skipped += 1
            continue
        data = src.read_bytes()
        figures_records.append(
            FigureRecord(
                path=src,
                source="figures-dir",
                label=str(src.relative_to(version_dir)),
                content_hash=_hash_bytes(data),
            )
        )
    if svg_skipped:
        reasons.append(
            f"{svg_skipped} SVG source(s) under figures/ recorded as "
            f"unverified; the VLM consumes raster bytes (the SVG path "
            f"would require an svg2png conversion not yet shipped)."
        )
    records.extend(figures_records)

    # Pick the rendered_artifact label for the Review schema field.
    if pdf is not None:
        rendered_artifact = pdf.name
    elif figures_records:
        rendered_artifact = "figures/"
    else:
        # Schema requires the field set; surface "no source" placeholder so
        # the Review still validates. The reviewer reading this can see at
        # a glance the critic ran on an empty surface.
        rendered_artifact = "(none)"

    return records, rendered_artifact, reasons


# ---------------------------------------------------------------------------
# VLM cache (session-lifetime, in-process)
# ---------------------------------------------------------------------------


class FigureVLMCache:
    """Session-lifetime in-memory cache: ``content_hash → VLM payload``.

    The cache is intentionally simple — a dict that lives for the lifetime
    of one ``critique_version_dir`` call (or longer if the caller hands the
    same cache instance into multiple calls). Eviction policy:
    **session-lifetime, no eviction within a session**. The caller controls
    cache lifetime by instantiating a fresh ``FigureVLMCache`` per session.

    The cached value is the raw VLM payload dict (the same shape
    :class:`VisionCritic.critique`'s callback receives), NOT a
    :class:`Review`. The Review is constructed per-figure with figure-
    specific context (label, version_dir, evidence_span) so the cache is
    payload-level not Review-level.

    Promotion path: when Phase 5 (``image-accessibility``, #341) reaches for
    this primitive, move it to ``anvil/lib/vision_cache.py`` and have both
    critics share. Until then it ships inline here per the coordination note
    in the #340 issue body.
    """

    def __init__(self) -> None:
        self._store: Dict[str, dict] = {}

    def get(self, content_hash: str) -> Optional[dict]:
        return self._store.get(content_hash)

    def put(self, content_hash: str, payload: dict) -> None:
        self._store[content_hash] = payload

    def __contains__(self, content_hash: str) -> bool:
        return content_hash in self._store

    def __len__(self) -> int:
        return len(self._store)


# ---------------------------------------------------------------------------
# Prompt (figure-content specific)
# ---------------------------------------------------------------------------


def build_figure_content_prompt(
    *,
    caption: Optional[str],
    adjacency: Optional[str],
    figure_label: str,
) -> str:
    """Build the VLM prompt for one figure's critique.

    Carries three load-bearing pieces of context:

    1. The brand palette (hex list) so the VLM scores ``on_brand`` against
       the documented palette, not its prior on "what looks corporate".
    2. The caption text (if any) so the VLM can score
       ``caption_grounding`` against the literal caption claim.
    3. The adjacent prose (if any) so the VLM can score
       ``adjacency_grounding`` against the surrounding claim.

    The prompt also enumerates the critical-flag taxonomy
    (``critical_figure_misrepresents_claim``) so the VLM can raise the
    flag by name when it detects a caption-vs-figure contradiction.
    """
    rubric = default_figure_content_rubric()
    lines: List[str] = []
    lines.append(
        "You are a figure-content critic evaluating a single rendered "
        "figure (chart, diagram, table, or image) against three scoring "
        "axes. Return ONE JSON object with the shape described."
    )
    lines.append("")
    lines.append(f"Figure label: {figure_label}")
    if caption:
        lines.append(f"Caption text: {caption}")
    if adjacency:
        lines.append(f"Adjacent prose: {adjacency}")
    lines.append("")
    lines.append("Brand palette (the figure SHOULD use these hex values):")
    for hex_val in _BRAND_PALETTE_HEX:
        lines.append(f"  - {hex_val}")
    lines.append(
        "Off-brand signals: matplotlib default tab10 (saturated blue, "
        "orange, green, red, purple, brown, pink, grey, olive, cyan); "
        "crimson / teal / magenta / gold as primary series colors."
    )
    lines.append("")
    lines.append("Rubric dimensions (score each 0..max):")
    for d in rubric.dimensions:
        lines.append(f"- {d.name} (0..{d.max}): {d.description}")
    lines.append("")
    lines.append("Critical-flag taxonomy (raise by type when applicable):")
    lines.append(
        f"- {CRITICAL_FIGURE_MISREPRESENTS_CLAIM}: the caption or adjacent "
        "prose claims something the figure does NOT depict (e.g. caption "
        "says 'revenue tripled' but the figure shows a flat line). This is "
        "the load-bearing critical flag; raise it whenever the visual "
        "content contradicts the textual claim."
    )
    lines.append("")
    lines.append("Return JSON ONLY (no markdown wrapper, no commentary):")
    lines.append(
        '{"scores": [{"dimension": "<name>", "score": <int|null>, '
        '"critical": <bool>, "justification": "<1-3 sentences>", '
        '"fix": "<one sentence|null>"}, ...], '
        '"findings": [{"severity": "blocker|major|minor|nit", '
        '"dimension": "<name|null>", "rationale": "<1-2 sentences>", '
        '"suggested_fix": "<one sentence>", '
        '"evidence_span": "<path>:figure=<label>|null"}, ...], '
        '"critical_flags": [{"type": "<flag-name>", '
        '"justification": "<one paragraph>", '
        '"evidence_span": "<path>:figure=<label>|null"}, ...]}'
    )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Per-figure critique
# ---------------------------------------------------------------------------


def _suggested_fix_for_dim(dim: str, score: int, max_: int) -> str:
    """Free-form ``Finding.suggested_fix`` text per-dimension.

    Stays within the existing ``Finding.suggested_fix`` contract (free
    string) — no schema delta per the #340 design contract. Phrasing
    matches the issue body's examples ("palette swap", "corrected
    caption", "drop or replace").
    """
    if dim == DIM_ON_BRAND:
        return (
            f"Swap the figure's palette to the Anvil brand colors "
            f"(navy / muted grey / navy tint / rule grey; see "
            f"anvil/lib/figures/palette.py). Apply "
            f"anvil/lib/figures/palette.apply() near the top of the "
            f"figure-generation script for matplotlib charts; for "
            f"hand-authored figures, edit the source to use the brand "
            f"hex values directly."
        )
    if dim == DIM_CAPTION_GROUNDING:
        return (
            f"Rewrite the caption to accurately describe what the figure "
            f"depicts. The current caption claims something the figure "
            f"does not show; either correct the claim or replace the "
            f"figure with one that supports the caption's intended "
            f"meaning."
        )
    if dim == DIM_ADJACENCY_GROUNDING:
        return (
            f"Drop or replace the figure. The surrounding prose makes a "
            f"claim the figure does not visibly support; either remove "
            f"the figure (and its prose hook) or substitute a figure that "
            f"clearly advances the adjacent claim."
        )
    return f"Address the dim={dim!r} score of {score}/{max_}."


def _payload_to_per_figure_outputs(
    payload: dict,
    *,
    figure: FigureRecord,
    rendered_artifact: str,
) -> tuple[List[Score], List[Finding], List[CriticalFlag]]:
    """Map one VLM payload to per-figure scores + findings + critical flags.

    The mapping mirrors :meth:`anvil.lib.vision.VisionCritic._payload_to_review`
    but flattens to lists for per-figure aggregation instead of building a
    Review. Score values are clamped to the rubric range defensively.
    """
    rubric = default_figure_content_rubric()
    scores: List[Score] = []
    findings: List[Finding] = []
    critical_flags: List[CriticalFlag] = []

    incoming_scores = {
        s.get("dimension"): s for s in payload.get("scores", [])
    }
    for dim in rubric.dimensions:
        entry = incoming_scores.get(dim.name) or {}
        raw_score = entry.get("score")
        if raw_score is not None:
            try:
                s_int: Optional[int] = int(raw_score)
            except (TypeError, ValueError):
                s_int = None
            else:
                s_int = max(0, min(dim.max, s_int))
        else:
            s_int = None
        is_critical = bool(entry.get("critical", False))
        scores.append(
            Score(
                dimension=dim.name,
                score=s_int,
                max=dim.max,
                critical=is_critical,
                fix=entry.get("fix") or None,
                justification=entry.get("justification") or None,
                evidence_span=f"{rendered_artifact}:figure={figure.label}",
            )
        )
        # Emit a Finding for any sub-threshold dim that lacks an explicit
        # severity-level Finding in the payload. The VLM-supplied findings
        # take precedence; this layer is a safety net for "low score with
        # no narrative entry", which would otherwise produce a silent dim
        # drop on the rolled-up Review.
        if s_int is not None and s_int <= dim.max // 2:
            findings.append(
                Finding(
                    severity="major" if s_int <= 1 else "minor",
                    dimension=dim.name,
                    rationale=(
                        entry.get("justification")
                        or f"figure-content {dim.name} scored {s_int}/{dim.max}"
                    ),
                    suggested_fix=(
                        entry.get("fix")
                        or _suggested_fix_for_dim(dim.name, s_int, dim.max)
                    ),
                    evidence_span=f"{rendered_artifact}:figure={figure.label}",
                )
            )

    for f in payload.get("findings", []) or []:
        sev = f.get("severity", "minor")
        if sev not in {"blocker", "major", "minor", "nit"}:
            sev = "minor"
        # Override evidence_span with the per-figure shape so all findings
        # carry a uniform locator. Tests assert on this format.
        findings.append(
            Finding(
                severity=sev,  # type: ignore[arg-type]
                dimension=f.get("dimension") or None,
                rationale=f.get("rationale", ""),
                suggested_fix=f.get("suggested_fix", ""),
                evidence_span=f.get("evidence_span")
                or f"{rendered_artifact}:figure={figure.label}",
            )
        )

    for cf in payload.get("critical_flags", []) or []:
        critical_flags.append(
            CriticalFlag(
                type=cf.get("type", "unspecified"),
                justification=cf.get("justification", ""),
                evidence_span=cf.get("evidence_span")
                or f"{rendered_artifact}:figure={figure.label}",
            )
        )

    return scores, findings, critical_flags


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------


def critique_version_dir(
    version_dir: Path,
    *,
    callback: Optional[VisionCallback] = None,
    model: Optional[str] = None,
    cache: Optional[FigureVLMCache] = None,
    vlm_budget_per_figure: int = DEFAULT_VLM_BUDGET_PER_FIGURE,
    figure_captions: Optional[Dict[str, str]] = None,
    figure_adjacency: Optional[Dict[str, str]] = None,
    pdf_dpi: int = 150,
    extract_dir: Optional[Path] = None,
) -> FigureContentResult:
    """Run the figure-content VLM critic over one version dir.

    The single public entry point. Discovers every figure (PDF page
    extraction + ``figures/`` dir walk), runs a VLM pass per unique
    content hash (with cache hit on repeat), and assembles a
    :class:`FigureContentResult` for downstream aggregation / persistence.

    Parameters
    ----------
    version_dir
        Path to ``<thread>.{N}/``. The PDF is discovered as
        ``<thread>.pdf`` (slug-echo per #295) or any single ``*.pdf`` in
        the directory. ``figures/`` is walked recursively.
    callback
        Optional ``VisionCallback`` for offline / test use. When ``None``,
        the default :class:`VisionCritic` path tries the Anthropic SDK
        (which requires ``anthropic`` + ``ANTHROPIC_API_KEY``). Tests
        ALWAYS pass a stub callback.
    model
        Anthropic model id surfaced on ``Review.model``. Defaults to the
        :class:`VisionCritic` default.
    cache
        Session-lifetime VLM payload cache. When ``None``, a fresh
        :class:`FigureVLMCache` is created and used for this call only.
    vlm_budget_per_figure
        Max VLM calls per unique figure (default ``1`` per the issue
        body). Repeat content hashes hit the cache regardless.
    figure_captions
        Optional ``{label: caption}`` map so the prompt can carry the
        caption text for the ``caption_grounding`` axis. The label is the
        :attr:`FigureRecord.label` value.
    figure_adjacency
        Optional ``{label: adjacent prose}`` map for the
        ``adjacency_grounding`` axis.
    pdf_dpi
        Rasterization DPI for PDF page extraction (default 150 — the
        :func:`render_pdf_to_pngs` default).
    extract_dir
        Optional caller-provided tempdir for extracted PNGs. When
        ``None``, a tempdir is created and not cleaned up — extracted PNGs
        survive the call so the caller can use the paths surfaced on
        :attr:`FigureRecord.path` for follow-on actions.

    Returns
    -------
    :class:`FigureContentResult` carrying per-figure scores + findings +
    critical flags + top-level reasons + VLM call / cache-hit counters.

    Raises
    ------
    FileNotFoundError
        When ``version_dir`` does not exist or is not a directory.
    """
    version_dir = Path(version_dir).resolve()
    if not version_dir.is_dir():
        raise FileNotFoundError(
            f"figure_content: version_dir {version_dir!s} does not exist "
            f"or is not a directory."
        )

    figure_captions = figure_captions or {}
    figure_adjacency = figure_adjacency or {}
    cache = cache if cache is not None else FigureVLMCache()

    records, rendered_artifact, reasons = discover_figures(
        version_dir, pdf_dpi=pdf_dpi, extract_dir=extract_dir
    )

    result = FigureContentResult(
        version_dir=version_dir.name,
        rendered_artifact=rendered_artifact,
        figures=records,
        reasons=list(reasons),
    )

    if not records:
        result.reasons.append(
            "no figures discovered (no PDF and no figures/ dir, or both "
            "empty); critic ran clean with zero VLM calls."
        )
        return result

    critic = VisionCritic(
        model=model or "claude-sonnet-4-5-20251022",
        callback=callback,
        critic_id=CRITIC_ID,
    )

    for figure in records:
        prompt = build_figure_content_prompt(
            caption=figure_captions.get(figure.label),
            adjacency=figure_adjacency.get(figure.label),
            figure_label=figure.label,
        )
        cached = cache.get(figure.content_hash)
        if cached is not None:
            payload = cached
            result.cache_hits += 1
        else:
            # Budget: per-figure cap. The default is 1; values > 1 would
            # let the caller sample the VLM repeatedly for noise reduction
            # (not exercised in v0).
            if vlm_budget_per_figure <= 0:
                result.reasons.append(
                    f"figure {figure.label!r}: vlm budget exhausted; "
                    f"skipping VLM pass for this figure."
                )
                continue
            if callback is not None:
                payload = callback([figure.path], prompt)
            else:
                # Lazy: call the critic's internal Anthropic path. We do
                # not construct a Review here — we only need the payload
                # so the per-figure aggregation can roll up later.
                payload = critic._call_anthropic([figure.path], prompt)
            cache.put(figure.content_hash, payload)
            result.vlm_calls += 1

        per_scores, per_findings, per_flags = _payload_to_per_figure_outputs(
            payload, figure=figure, rendered_artifact=rendered_artifact
        )
        result.scores.extend(per_scores)
        result.findings.extend(per_findings)
        result.critical_flags.extend(per_flags)

    return result


# ---------------------------------------------------------------------------
# Critic-sibling writer
# ---------------------------------------------------------------------------


def write_review_dir(
    version_dir: Path,
    result: FigureContentResult,
    *,
    critic_id: str = CRITIC_ID,
    model: Optional[str] = None,
) -> Path:
    """Write ``<version_dir>.figure-content/_review.json`` for auto-discovery.

    Delegates to the shared :func:`anvil.lib.sidecar.write_critic_review_dir`
    (issue #1086), which stages + atomically renames the sidecar via
    ``staged_sidecar`` (issue #350) — a mid-write interrupt never leaves a
    partial ``<version_dir>.figure-content/`` at the final name. This is a
    behavior change from the pre-#1086 plain ``mkdir`` + ``write_text``
    shape (called out explicitly in the #1086 PR body); the consuming
    ``memo-figure-content.md`` / ``report-figure-content.md`` docs already
    mandated ``staged_sidecar`` for this critic, so the change closes a
    doc/code drift rather than introducing a new contract. Returns the
    path to the written ``_review.json``.

    The naming convention (``<version_dir>.figure-content/``) follows the
    same ``<version_dir>.<tag>/`` pattern that
    :func:`anvil.lib.critics.discover_critics` recognizes without code
    changes (the convention exercised by Phase 2's ``.hyperlinks/`` and
    Phase 3's ``.citations/`` siblings).
    """
    version_dir = Path(version_dir)
    review = result.to_review(
        version_dir=version_dir.name, critic_id=critic_id, model=model
    )
    return write_critic_review_dir(version_dir, SIBLING_SUFFIX, review)


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------


def _build_cli_parser() -> "object":
    """Build the argparse parser. Factored out for testability."""
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.figure_content",
        description=(
            "Figure-content VLM critic. Walks every figure in a memo or "
            "report version dir (PDF page extraction via pdftoppm + "
            "figures/ dir sources) and scores three axes per figure: "
            "on-brand palette match, caption grounding, adjacency "
            "grounding. Requires a callback for offline / CI use; otherwise "
            "uses the Anthropic SDK (ANTHROPIC_API_KEY required)."
        ),
    )
    p.add_argument(
        "version_dir",
        help="Path to <thread>.{N}/ containing the figures to critique.",
    )
    p.add_argument(
        "--write-review",
        action="store_true",
        help=(
            "Also write <version_dir>.figure-content/_review.json for "
            "critic-sibling auto-discovery by aggregate()."
        ),
    )
    p.add_argument(
        "--pdf-dpi",
        type=int,
        default=150,
        help="Rasterization DPI for PDF page extraction (default 150).",
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Returns the process exit code.

    Exit codes (mirroring Phase 2 / Phase 3 precedents):

    - ``0``: clean pass (no findings, no critical flag).
    - ``1``: one or more findings (or a critical flag).
    - ``2``: invocation error (missing version_dir).
    """
    parser = _build_cli_parser()
    args = parser.parse_args(argv)
    try:
        result = critique_version_dir(
            Path(args.version_dir),
            pdf_dpi=args.pdf_dpi,
        )
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result.to_json(), indent=2))
    if args.write_review:
        out = write_review_dir(Path(args.version_dir), result)
        print(f"wrote {out}", file=sys.stderr)
    return 0 if result.passed() else 1


__all__ = [
    "CRITIC_ID",
    "SIBLING_SUFFIX",
    "RUBRIC_ID",
    "CRITICAL_FIGURE_MISREPRESENTS_CLAIM",
    "DIM_ON_BRAND",
    "DIM_CAPTION_GROUNDING",
    "DIM_ADJACENCY_GROUNDING",
    "DEFAULT_VLM_BUDGET_PER_FIGURE",
    "FigureRecord",
    "FigureContentResult",
    "FigureVLMCache",
    "check_pdftoppm_available",
    "default_figure_content_rubric",
    "discover_figures",
    "build_figure_content_prompt",
    "critique_version_dir",
    "write_review_dir",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
