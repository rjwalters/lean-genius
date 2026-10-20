"""Tests for the paper-vision critic wiring.

This exercises the paper skill's vision integration against a fixture paper
that reproduces the four paper-relevant rendered-only defect families:

- mathtext_artifacts (highest-stakes: ``$11B`` rendered as italic math —
  a correctness defect because LaTeX is source-of-truth).
- label_cropping / table overflow (a wide results table clipped at the
  right margin, dropping the best-result column).
- axis_legibility (a scaling plot's tick labels illegible at print size).
- palette_adherence (raw matplotlib defaults; color-only encoding).

The VLM call is stubbed with a callback that simulates the expected
detection. Real Anthropic calls are out of scope for this test (see
``tests/lib/test_vision.py`` for the opt-in smoke path).

The paper vision rubric is a FOUR-dimension subset of the framework's
shipped six (``vertical_overflow`` and ``slide_density`` are slide-centric
and dropped for a paginated paper), composed via ``VisionRubric``.

The file is named ``test_paper_vision.py`` (not ``test_vision.py``) to avoid
the pytest rootdir filename-collision across skills.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Dict, List

import pytest


# Ensure repo root is importable. This file lives at
# anvil/skills/paper/tests/test_paper_vision.py — four levels deep from the
# repo root (tests -> paper -> skills -> anvil -> <root>).
_HERE = Path(__file__).resolve().parent
_REPO_ROOT = _HERE.parents[3]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from anvil.lib.critics import (  # noqa: E402
    aggregate,
    discover_critics,
    load_review,
)
from anvil.lib.review_schema import Kind, Verdict  # noqa: E402
from anvil.lib.vision import (  # noqa: E402
    CRITICAL_FLAG_MATHTEXT_ARTIFACT_BREAKS_MEANING,
    CRITICAL_FLAG_RENDERED_OVERFLOW_UNRECOVERABLE,
    DEFAULT_VISION_DIMENSIONS,
    VisionCritic,
    VisionRubric,
)


FIXTURES = _HERE / "fixtures" / "vision"

# The paper-vision critic owns exactly these four dims (a subset of the
# shipped six). Keep this list in lockstep with commands/paper-vision.md.
PUB_VISION_DIM_NAMES = (
    "label_cropping",
    "axis_legibility",
    "palette_adherence",
    "mathtext_artifacts",
)


def pub_vision_rubric() -> VisionRubric:
    """The four-dim paper-vision rubric, narrowed from the shipped six."""
    dims = [d for d in DEFAULT_VISION_DIMENSIONS if d.name in PUB_VISION_DIM_NAMES]
    return VisionRubric(dimensions=dims, rubric_id="anvil-pub-vision-v1")


def _clean_score_row(dim_name: str, max: int) -> Dict:
    return {
        "dimension": dim_name,
        "score": max - 1,
        "critical": False,
        "justification": "Default clean score for this fixture.",
        "fix": None,
    }


def _baseline_payload(rubric: VisionRubric) -> Dict:
    """An "all clean" payload (over the rubric's dims) that fixtures perturb."""
    return {
        "scores": [_clean_score_row(d.name, d.max) for d in rubric.dimensions],
        "findings": [],
        "critical_flags": [],
    }


def _make_stub_for_paper_defects(images, prompt):
    """Stub returning the expected detection for the smoke fixture.

    Reproduces all four paper-relevant defect families at once (one fixture,
    one render): mathtext + table overflow as critical flags; axis
    legibility + palette adherence as findings.
    """
    rubric = pub_vision_rubric()
    payload = _baseline_payload(rubric)

    for s in payload["scores"]:
        if s["dimension"] == "mathtext_artifacts":
            s["score"] = 0
            s["critical"] = True
            s["justification"] = (
                "'$11B' in the title and '$40k' in the Results render as "
                "italic math with no dollar sign (the $ opens a math span). "
                "LaTeX is source-of-truth, so this changes the claim."
            )
            s["fix"] = (
                "Escape the dollar signs (`\\$11B`, `\\$40k`) or use a "
                "non-math currency macro."
            )
        if s["dimension"] == "label_cropping":
            s["score"] = 1
            s["critical"] = True
            s["justification"] = (
                "Table 1's 7th column 'Best-F1 (95% CI)' crosses the page's "
                "right margin; the load-bearing best-result column is clipped."
            )
            s["fix"] = (
                "Wrap the tabular in \\resizebox{\\textwidth}{!}{...} or move "
                "to a two-row \\multicolumn layout."
            )
        if s["dimension"] == "axis_legibility":
            s["score"] = 2
            s["justification"] = (
                "fig-scaling.pdf tick labels are ~5pt at print size — "
                "illegible at 100% on the rendered page."
            )
            s["fix"] = "Bump tick/label fontsize in figures/src/fig-scaling.py."
        if s["dimension"] == "palette_adherence":
            s["score"] = 2
            s["justification"] = (
                "Plot uses raw matplotlib defaults; the two series differ "
                "only by color and collapse in grayscale print."
            )
            s["fix"] = (
                "Set a print-safe color cycle and add a linestyle/marker "
                "distinction in figures/src/fig-scaling.py."
            )

    payload["critical_flags"] = [
        {
            "type": CRITICAL_FLAG_MATHTEXT_ARTIFACT_BREAKS_MEANING,
            "justification": (
                "The corpus-size and training-cost figures render without "
                "their dollar signs; a reader cannot parse them as the "
                "monetary/scale claims the authors intended."
            ),
            "evidence_span": "paper.pdf:page=1",
        },
        {
            "type": CRITICAL_FLAG_RENDERED_OVERFLOW_UNRECOVERABLE,
            "justification": (
                "Table 1's best-result column is clipped at the page margin; "
                "the headline F1 numbers a reviewer needs are not on the page."
            ),
            "evidence_span": "paper.pdf:page=2",
        },
    ]

    payload["findings"] = [
        {
            "severity": "major",
            "dimension": "axis_legibility",
            "rationale": "Figure 1 axis tick labels illegible at print size.",
            "suggested_fix": "Increase tick/label fontsize and re-render.",
            "evidence_span": "paper.pdf:page=2",
        },
        {
            "severity": "minor",
            "dimension": "palette_adherence",
            "rationale": "Figure 1 uses default matplotlib palette; color-only.",
            "suggested_fix": "Print-safe palette + linestyle distinction.",
            "evidence_span": "paper.pdf:page=2",
        },
    ]
    return payload


# ---------------------------------------------------------------------------
# Fixture + rubric shape
# ---------------------------------------------------------------------------


def test_fixture_paper_present():
    """The smoke fixture paper exists under the fixtures dir."""
    assert (FIXTURES / "repro_paper_render_defects.md").exists()


def test_paper_rubric_is_four_dim_subset():
    """The paper rubric narrows the shipped six to four paper-relevant dims."""
    rubric = pub_vision_rubric()
    names = [d.name for d in rubric.dimensions]
    assert names == list(PUB_VISION_DIM_NAMES) or set(names) == set(
        PUB_VISION_DIM_NAMES
    )
    # The two slide-centric dims are NOT owned by the paper critic.
    assert "vertical_overflow" not in names
    assert "slide_density" not in names
    # Four dims, /20 total.
    assert len(rubric.dimensions) == 4
    assert rubric.max_total() == 20


# ---------------------------------------------------------------------------
# Critique: stub-driven detection
# ---------------------------------------------------------------------------


def test_vision_detects_paper_render_defects(tmp_path):
    """The paper-vision critic surfaces all four defect families from the stub."""
    page = tmp_path / "page-1.png"
    page.write_bytes(b"\x89PNG fake")

    critic = VisionCritic(
        critic_id="paper-vision",
        callback=_make_stub_for_paper_defects,
    )
    review = critic.critique(
        images=[page],
        rubric=pub_vision_rubric(),
        version_dir="q3-method.1",
        rendered_artifact="paper.pdf",
    )

    assert review.kind == Kind.VISION
    assert review.rendered_artifact == "paper.pdf"
    assert review.critic_id == "paper-vision"
    assert review.rubric == "anvil-pub-vision-v1"

    by_dim = {s.dimension: s for s in review.scores}

    # mathtext is the highest-stakes dim: scored 0 + critical.
    assert by_dim["mathtext_artifacts"].score == 0
    assert by_dim["mathtext_artifacts"].critical is True

    # table overflow surfaces under label_cropping + critical.
    assert by_dim["label_cropping"].score == 1
    assert by_dim["label_cropping"].critical is True

    # figure-legibility findings (non-critical dims).
    assert by_dim["axis_legibility"].score == 2
    assert by_dim["palette_adherence"].score == 2

    # Both shipped critical-flag types are raised.
    flags = {cf.type for cf in review.critical_flags}
    assert CRITICAL_FLAG_MATHTEXT_ARTIFACT_BREAKS_MEANING in flags
    assert CRITICAL_FLAG_RENDERED_OVERFLOW_UNRECOVERABLE in flags

    # Two findings (axis_legibility major + palette_adherence minor).
    severities = {f.severity for f in review.findings}
    assert "major" in severities
    assert "minor" in severities


def test_vision_review_serializes_round_trip(tmp_path):
    """The Review serializes to canonical _review.json and reloads cleanly."""
    page = tmp_path / "page-1.png"
    page.write_bytes(b"\x89PNG fake")

    critic = VisionCritic(
        critic_id="paper-vision",
        callback=_make_stub_for_paper_defects,
    )
    review = critic.critique(
        images=[page],
        rubric=pub_vision_rubric(),
        version_dir="q3-method.1",
        rendered_artifact="paper.pdf",
    )

    out = tmp_path / "_review.json"
    out.write_text(review.model_dump_json(indent=2))
    assert out.exists()
    reloaded = type(review).model_validate_json(out.read_text())
    assert reloaded.kind == Kind.VISION
    assert reloaded.critic_id == "paper-vision"


# ---------------------------------------------------------------------------
# Discovery + aggregation via anvil/lib/critics.py
# ---------------------------------------------------------------------------


def test_vision_sibling_discovers_and_aggregates(tmp_path):
    """AC: the vision critic discovers + aggregates cleanly via critics.py.

    Lay out a version dir + a `.vision/` sibling carrying a real
    `_review.json`, then confirm `discover_critics` finds it, `load_review`
    reads it back as `kind=vision`, and `aggregate` short-circuits the
    verdict to BLOCK on the vision critical flags.
    """
    portfolio = tmp_path
    version_dir = portfolio / "q3-method.1"
    version_dir.mkdir()
    (version_dir / "main.tex").write_text("\\documentclass{anvil-paper}\n")

    vision_dir = portfolio / "q3-method.1.vision"
    vision_dir.mkdir()

    page = vision_dir / "page-1.png"
    page.write_bytes(b"\x89PNG fake")

    critic = VisionCritic(
        critic_id="paper-vision",
        callback=_make_stub_for_paper_defects,
    )
    review = critic.critique(
        images=[page],
        rubric=pub_vision_rubric(),
        version_dir="q3-method.1",
        rendered_artifact="paper.pdf",
    )
    (vision_dir / "_review.json").write_text(review.model_dump_json(indent=2))

    # Discovery: the .vision sibling is found (tag = "vision").
    found = discover_critics(version_dir)
    assert vision_dir in found

    # Load: round-trips back to a vision Review.
    loaded = load_review(vision_dir)
    assert loaded.kind == Kind.VISION
    assert loaded.critic_id == "paper-vision"

    # Aggregate: the vision critical flags force a BLOCK verdict.
    agg = aggregate([loaded])
    assert agg.verdict == Verdict.BLOCK
    flag_types = {cf.type for cf in agg.critical_flags}
    assert CRITICAL_FLAG_MATHTEXT_ARTIFACT_BREAKS_MEANING in flag_types
    assert CRITICAL_FLAG_RENDERED_OVERFLOW_UNRECOVERABLE in flag_types


# ---------------------------------------------------------------------------
# Command spec presence
# ---------------------------------------------------------------------------


def test_paper_vision_command_spec_exists():
    """AC: anvil/skills/paper/commands/paper-vision.md is present + canonical."""
    cmd = (
        _REPO_ROOT
        / "anvil"
        / "skills"
        / "paper"
        / "commands"
        / "paper-vision.md"
    )
    assert cmd.exists()
    text = cmd.read_text()

    # The four owned dims are documented.
    for name in PUB_VISION_DIM_NAMES:
        assert name in text

    # The two slide-centric dims it deliberately drops are named as dropped.
    assert "vertical_overflow" in text
    assert "slide_density" in text

    # The two shipped critical-flag types are documented.
    assert CRITICAL_FLAG_RENDERED_OVERFLOW_UNRECOVERABLE in text
    assert CRITICAL_FLAG_MATHTEXT_ARTIFACT_BREAKS_MEANING in text

    # The canonical progress/meta/review shapes are referenced.
    assert "_progress.json" in text
    assert "_meta.json" in text
    assert "_review.json" in text

    # The pandoc render path is referenced (paper renders prose, not Marp).
    assert "render_pandoc_to_pdf" in text
    assert "render_pdf_to_pngs" in text


def test_paper_revise_documents_vision_d6_note():
    """AC: paper-revise.md carries the D6 vision-findings note."""
    revise = (
        _REPO_ROOT
        / "anvil"
        / "skills"
        / "paper"
        / "commands"
        / "paper-revise.md"
    )
    text = revise.read_text()
    assert "paper-vision" in text
    # The note must steer fixes to figure source / LaTeX structure, not prose.
    assert "figures/src" in text
    assert "kind=vision" in text


def test_paper_rubric_documents_vision_dims():
    """AC: rubric.md documents the vision-owned dimensions."""
    rubric_md = _REPO_ROOT / "anvil" / "skills" / "paper" / "rubric.md"
    text = rubric_md.read_text()
    for name in PUB_VISION_DIM_NAMES:
        assert name in text
    # The overlay must be documented as additive, not part of the main gate.
    # Post-#357 the paper rubric ships at /44 (dim 9 *Rhetorical economy*).
    assert "/44" in text


def test_skill_dispatch_table_lists_pub_vision():
    """AC: SKILL.md command dispatch table includes paper-vision."""
    skill = _REPO_ROOT / "anvil" / "skills" / "paper" / "SKILL.md"
    text = skill.read_text()
    assert "paper-vision" in text
