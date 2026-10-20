"""Regression test: the underclaiming vs. bold-synthesis fixture pair (issue #1048).

``anvil/skills/paper/examples/`` ships two hand-authored ``anvil:paper``
projects that report **the same synthetic study, with the same evidence and
the same bibliography, framed two ways** (issue #1046 → #1047 → #1048):

* ``underclaiming-buried-lede/`` — rigorous, fully sourced, heavily qualified,
  organizing idea demoted to the last paragraph of the Discussion. Recorded
  review: **33/44, advance: false**, with a named ``underclaiming_buried_lede``
  finding at ``blocker`` severity.
* ``bold-synthesis-labeled/`` — the same work with a synthesis claim in the
  title and the first sentence and each contribution labelled
  demonstrated / derived / synthesis / conjecture. Recorded review:
  **43/44, advance: true**, with **no** overclaiming deduction.

The load-bearing property is not either score on its own. It is that the pair
holds evidence constant and varies only framing: the
``\\section{Method}``-through-``\\section{Experiments}`` span of the two bodies
is byte-identical, the two ``refs.bib`` files are byte-identical, the two
thread briefs' ``## Strongest claim`` sections are byte-identical, and the two
recorded reviews therefore score identically on dims 1, 2, 5, 6, and 8. The
whole 10-point gap sits in dims 3, 4, 7, and 9 — the framing dimensions #1047
made symmetric.

**What this test can and cannot pin.** The scores are recorded reviewer
judgment, not a deterministic computation (``examples/README.md`` §"Provenance
of the scores"), the same posture the ``essay`` / ``primer`` / ``spec`` worked
examples take and the same tension ``paper-audit``'s vision-owned dimensions
navigate. So the assertions below pin the recorded judgment's *shape* — below
threshold with the named finding and full marks on rigor/evidence/citation
hygiene on one side, at-or-above threshold with no overclaiming deduction on
the other — plus every mechanically checkable invariant (file manifest, rubric
stamps, scorecard arithmetic, shared-span equality, and verbatim quoted
evidence via ``anvil/lib/evidence_check.py``).

Per the #58 packaging convention this filename
(``test_paper_underclaiming_fixtures.py``) is unique across the
``anvil/skills/*/tests/`` tree.

Runs under either ``pytest anvil/skills/paper/tests/`` or
``python -m unittest discover anvil/skills/paper/tests/``.
"""

from __future__ import annotations

import json
import re
import unittest
from pathlib import Path
from typing import Dict, List

from anvil.lib.critics import parse_memo_scoring_table
from anvil.lib.evidence_check import check_version_dir
from anvil.lib.project_brief import ArtifactType, load_project_brief_strict


_EXAMPLES = Path(__file__).resolve().parent.parent / "examples"

# (project dir, thread slug)
_BURIED = ("underclaiming-buried-lede", "build-cache-miss-study")
_BOLD = ("bold-synthesis-labeled", "build-latency-history-problem")

_ADVANCE_THRESHOLD = 35
_RUBRIC_ID = "anvil-pub-v2"
_RUBRIC_TOTAL = 44

# The recorded reviewer judgment. Pinned exactly: a fixture edit that moves a
# score must move this table too, deliberately.
_RECORDED: Dict[str, Dict[str, int]] = {
    _BURIED[1]: {
        "Rigor of method / argument": 6,
        "Evidence sufficiency": 6,
        "Clarity of contribution": 1,
        "Related-work positioning": 3,
        "Reproducibility": 5,
        "Figure & table quality": 3,
        "Prose & structural quality": 3,
        "Citation hygiene": 5,
        "Rhetorical economy": 1,
    },
    _BOLD[1]: {
        "Rigor of method / argument": 6,
        "Evidence sufficiency": 6,
        "Clarity of contribution": 5,
        "Related-work positioning": 5,
        "Reproducibility": 5,
        "Figure & table quality": 3,
        "Prose & structural quality": 4,
        "Citation hygiene": 5,
        "Rhetorical economy": 4,
    },
}

# Dimensions the two fixtures share by construction (identical method,
# experiments, tables, and bibliography). A divergence here means the pair has
# stopped isolating framing.
_SHARED_EVIDENCE_DIMS = (
    "Rigor of method / argument",
    "Evidence sufficiency",
    "Reproducibility",
    "Figure & table quality",
    "Citation hygiene",
)

# The dimensions #1047 made symmetric; the whole score gap must live here.
_FRAMING_DIMS = (
    "Clarity of contribution",
    "Related-work positioning",
    "Prose & structural quality",
    "Rhetorical economy",
)

# The six questions paper-draft.md §"Strongest-claim inventory" requires, plus
# the two additional statements that section asks for.
_INVENTORY_ANCHORS = (
    "**Strongest honest statement**",
    "**Why a thoughtful reader might find it surprising or generative**",
    "**What it could inspire**",
    "**Demonstrated / derived / synthesis / conjecture split**",
    "**Opening organized around the strongest claim",
    "**Intellectual territory on success**",
    "**Reader should remember**",
    "**Deliberately excluded for focus**",
)

_REVIEW_MANIFEST = (
    "verdict.md",
    "scoring.md",
    "comments.md",
    "findings.md",
    "_summary.md",
    "_meta.json",
    "_progress.json",
)


def _project_dir(fixture) -> Path:
    return _EXAMPLES / fixture[0]


def _thread_dir(fixture) -> Path:
    return _EXAMPLES / fixture[0] / fixture[1]


def _version_dir(fixture) -> Path:
    return _thread_dir(fixture) / f"{fixture[1]}.1"


def _review_dir(fixture) -> Path:
    return _thread_dir(fixture) / f"{fixture[1]}.1.review"


def _scores(fixture) -> Dict[str, int]:
    """Parse the recorded ``scoring.md`` table into {dimension: score}."""
    rows = parse_memo_scoring_table(
        (_review_dir(fixture) / "scoring.md").read_text(encoding="utf-8")
    )
    return {r.dimension: r.score for r in rows if r.score is not None}


def _weights(fixture) -> Dict[str, int]:
    rows = parse_memo_scoring_table(
        (_review_dir(fixture) / "scoring.md").read_text(encoding="utf-8")
    )
    return {r.dimension: r.max for r in rows}


def _summary_block(fixture, heading: str) -> dict:
    """Read one ``## <heading>`` fenced-json block from ``_summary.md``."""
    text = (_review_dir(fixture) / "_summary.md").read_text(encoding="utf-8")
    match = re.search(
        rf"^##\s+{re.escape(heading)}\s*$.*?```json\s*\n(?P<body>.*?)\n```",
        text,
        re.DOTALL | re.MULTILINE,
    )
    if match is None:  # pragma: no cover — assertion failure path
        raise AssertionError(
            f"{fixture[1]}/_summary.md has no '## {heading}' json block"
        )
    return json.loads(match.group("body"))


def _shared_span(body: str) -> str:
    """The Method-through-Experiments span, from the document body only.

    Anchored after ``\\begin{document}`` so the fixtures' leading ``%%``
    provenance comments can mention the sections by name without
    perturbing the extraction.
    """
    start_of_doc = body.index(r"\begin{document}")
    doc = body[start_of_doc:]
    return doc[doc.index(r"\section{Method}"): doc.index(r"\section{Discussion}")]


def _strongest_claim_section(brief: str) -> str:
    """The brief's ``## Strongest claim`` section body.

    Anchored to a line-start heading so the fixtures' prose can refer to the
    section by name (inside backticks) without perturbing the extraction.
    """
    match = re.search(r"^## Strongest claim\s*$", brief, re.MULTILINE)
    if match is None:  # pragma: no cover — assertion failure path
        raise AssertionError("brief has no '## Strongest claim' heading")
    rest = brief[match.end():]
    end = rest.index("\n## ")
    return rest[:end]


class TestFixturePairStructure(unittest.TestCase):
    """The two fixture projects exist and parse as paper projects."""

    def test_examples_dir_ships_both_fixtures(self) -> None:
        for fixture in (_BURIED, _BOLD):
            self.assertTrue(
                (_project_dir(fixture) / "BRIEF.md").is_file(),
                f"expected a project BRIEF at {_project_dir(fixture)}",
            )
        self.assertTrue((_EXAMPLES / "README.md").is_file())

    def test_project_briefs_parse_strict_as_paper(self) -> None:
        for fixture in (_BURIED, _BOLD):
            brief = load_project_brief_strict(_project_dir(fixture))
            self.assertEqual(brief.project, fixture[0])
            doc = next(d for d in brief.documents if d.slug == fixture[1])
            self.assertEqual(doc.artifact_type, ArtifactType.PAPER)

    def test_version_dirs_carry_the_paper_body_manifest(self) -> None:
        for fixture in (_BURIED, _BOLD):
            vdir = _version_dir(fixture)
            for name in ("main.tex", "refs.bib", "_progress.json"):
                self.assertTrue(
                    (vdir / name).is_file(), f"expected {name} in {vdir}"
                )
            prog = json.loads((vdir / "_progress.json").read_text())
            self.assertEqual(prog["version"], 1)
            self.assertEqual(prog["phases"]["draft"]["state"], "done")
            self.assertEqual(prog["metadata"]["artifact_type"], "paper")

    def test_review_siblings_carry_the_full_manifest(self) -> None:
        for fixture in (_BURIED, _BOLD):
            rdir = _review_dir(fixture)
            for name in _REVIEW_MANIFEST:
                self.assertTrue(
                    (rdir / name).is_file(), f"expected {name} in {rdir}"
                )

    def test_review_meta_carries_the_paper_rubric_stamps(self) -> None:
        # paper is a /44 rubric on the general >=35 band (SKILL.md
        # §"State machine"); the #346 per-review version stamps must land.
        for fixture in (_BURIED, _BOLD):
            meta = json.loads((_review_dir(fixture) / "_meta.json").read_text())
            self.assertEqual(meta["scorecard_kind"], "human-verdict")
            self.assertEqual(meta["rubric_id"], _RUBRIC_ID)
            self.assertEqual(meta["rubric_total"], _RUBRIC_TOTAL)
            self.assertEqual(meta["advance_threshold"], _ADVANCE_THRESHOLD)


class TestEvidenceHeldConstant(unittest.TestCase):
    """The pair varies framing ONLY — the evidence is literally the same text.

    Without these invariants the score gap could be explained by one fixture
    simply being a better paper, and the pair would prove nothing about the
    #1047 criteria.
    """

    def test_method_through_experiments_span_is_byte_identical(self) -> None:
        buried = _shared_span(
            (_version_dir(_BURIED) / "main.tex").read_text(encoding="utf-8")
        )
        bold = _shared_span(
            (_version_dir(_BOLD) / "main.tex").read_text(encoding="utf-8")
        )
        self.assertGreater(len(buried), 2000, "the shared span should be substantial")
        self.assertEqual(
            buried,
            bold,
            "the Method-through-Experiments span must stay byte-identical "
            "across the two fixtures — it is what makes the score divergence "
            "attributable to framing alone. Edit both fixtures or neither.",
        )

    def test_bibliographies_are_byte_identical(self) -> None:
        self.assertEqual(
            (_version_dir(_BURIED) / "refs.bib").read_text(encoding="utf-8"),
            (_version_dir(_BOLD) / "refs.bib").read_text(encoding="utf-8"),
            "both fixtures must cite the same literature so dim 8 cannot be "
            "the source of their score divergence",
        )

    def test_both_thread_briefs_answer_the_strongest_claim_inventory(self) -> None:
        # paper-draft.md §"Strongest-claim inventory" (#1047) requires the
        # brief to answer six questions plus the remember/excluded statements.
        for fixture in (_BURIED, _BOLD):
            brief = (_thread_dir(fixture) / "BRIEF.md").read_text(encoding="utf-8")
            self.assertIn("## Strongest claim", brief)
            for anchor in _INVENTORY_ANCHORS:
                self.assertIn(
                    anchor,
                    brief,
                    f"{fixture[1]}/BRIEF.md is missing the inventory answer "
                    f"{anchor!r}",
                )

    def test_strongest_claim_sections_are_byte_identical(self) -> None:
        # The shared yardstick: both drafts were briefed on the SAME
        # organizing idea, so "the paper does not match its own brief" is a
        # checkable statement about fixture A rather than a difference in
        # what the two authors set out to claim.
        self.assertEqual(
            _strongest_claim_section(
                (_thread_dir(_BURIED) / "BRIEF.md").read_text(encoding="utf-8")
            ),
            _strongest_claim_section(
                (_thread_dir(_BOLD) / "BRIEF.md").read_text(encoding="utf-8")
            ),
        )

    def test_quoted_evidence_is_verbatim_in_both_bodies(self) -> None:
        # Every dimension justification in both scoring.md files must quote
        # main.tex verbatim (issue #464/#475 discipline, enforced by
        # anvil/lib/evidence_check.py). A recorded review anchored to text
        # that does not exist would not be evidence of anything.
        for fixture in (_BURIED, _BOLD):
            result = check_version_dir(_version_dir(fixture))
            self.assertEqual(
                result.dimensions_checked,
                9,
                f"{fixture[1]}: expected all 9 rubric dims checked",
            )
            self.assertTrue(
                result.passed(),
                f"{fixture[1]}: evidence check findings: "
                f"{[f.to_dict() for f in result.findings]}",
            )


class TestRecordedScoring(unittest.TestCase):
    """The recorded scorecards are arithmetically sound and land as claimed."""

    def test_recorded_scores_match_the_pinned_table(self) -> None:
        for fixture in (_BURIED, _BOLD):
            self.assertEqual(_scores(fixture), _RECORDED[fixture[1]])

    def test_scorecard_arithmetic_is_self_consistent(self) -> None:
        # Sum of the 9 dimension scores == the total the verdict, _summary.md,
        # and _progress.json all claim; weights sum to the /44 rubric total.
        expected = {_BURIED[1]: 33, _BOLD[1]: 43}
        for fixture in (_BURIED, _BOLD):
            scores = _scores(fixture)
            total = sum(scores.values())
            self.assertEqual(total, expected[fixture[1]])
            self.assertEqual(sum(_weights(fixture).values()), _RUBRIC_TOTAL)

            summary = _summary_block(fixture, "Scores")
            self.assertEqual(summary["total"], total)

            prog = json.loads(
                (_review_dir(fixture) / "_progress.json").read_text()
            )
            self.assertEqual(prog["metadata"]["total_score"], total)
            self.assertEqual(prog["metadata"]["critical_flags"], 0)

            verdict = (_review_dir(fixture) / "verdict.md").read_text(
                encoding="utf-8"
            )
            self.assertIn(f"**{total}/44**", verdict)

    def test_evidence_dims_score_identically_across_the_pair(self) -> None:
        buried, bold = _scores(_BURIED), _scores(_BOLD)
        for dim in _SHARED_EVIDENCE_DIMS:
            self.assertEqual(
                buried[dim],
                bold[dim],
                f"dim {dim!r} must score identically in both fixtures — the "
                f"evidence behind it is literally the same text",
            )

    def test_the_entire_score_gap_lives_in_the_framing_dims(self) -> None:
        buried, bold = _scores(_BURIED), _scores(_BOLD)
        gap = sum(bold.values()) - sum(buried.values())
        framing_gap = sum(bold[d] - buried[d] for d in _FRAMING_DIMS)
        self.assertEqual(gap, 10)
        self.assertEqual(
            gap,
            framing_gap,
            "every point separating the two fixtures must come from dims 3, "
            "4, 7, and 9 (clarity of contribution, related-work positioning, "
            "prose/structure, rhetorical economy)",
        )


class TestBuriedFixtureFailsForTheRightReason(unittest.TestCase):
    """Fixture A: below threshold on framing, full marks on rigor/evidence."""

    def test_scores_below_the_advance_threshold(self) -> None:
        total = sum(_scores(_BURIED).values())
        self.assertLess(
            total,
            _ADVANCE_THRESHOLD,
            "the buried-contribution fixture must fail the >=35 gate — if it "
            "creeps above, caution has become cheap again and #1047's dim 3 / "
            "dim 9 symmetry has regressed",
        )
        self.assertFalse(_summary_block(_BURIED, "Scores")["advance"])
        self.assertIn(
            "advance: false",
            (_review_dir(_BURIED) / "verdict.md").read_text(encoding="utf-8"),
        )

    def test_still_scores_well_on_rigor_evidence_and_citation_hygiene(self) -> None:
        # The whole point: this is not a bad paper. It fails anyway.
        scores, weights = _scores(_BURIED), _weights(_BURIED)
        for dim in (
            "Rigor of method / argument",
            "Evidence sufficiency",
            "Reproducibility",
            "Citation hygiene",
        ):
            self.assertEqual(
                scores[dim],
                weights[dim],
                f"the buried fixture must hold FULL weight on {dim!r} — a "
                f"fixture that also failed on rigor would prove nothing",
            )

    def test_the_named_underclaiming_finding_is_recorded(self) -> None:
        block = _summary_block(_BURIED, "underclaiming_check")
        self.assertTrue(block["ran"])
        finding = block["finding"]
        self.assertIsNotNone(finding, "the named finding must be recorded")
        self.assertEqual(finding["type"], "underclaiming_buried_lede")
        self.assertEqual(finding["severity"], "blocker")
        self.assertEqual(sorted(finding["dimensions"]), [3, 9])

        cold = block["cold_reader"]
        self.assertFalse(cold["central_idea_extractable_from_abstract_and_intro"])
        self.assertFalse(cold["extractable_idea_matches_brief_strongest_claim"])
        self.assertFalse(cold["claim_stated_before_qualification_apparatus"])

        comments = (_review_dir(_BURIED) / "comments.md").read_text(
            encoding="utf-8"
        )
        self.assertIn("underclaiming_buried_lede", comments)
        self.assertIn("**blocker**", comments)

        prog = json.loads((_review_dir(_BURIED) / "_progress.json").read_text())
        self.assertIn("underclaiming_buried_lede", prog["metadata"]["named_findings"])

    def test_framing_dims_are_at_or_below_a_quarter_weight(self) -> None:
        # rubric.md's calibration: ~25% of weight is "present but inadequate".
        scores, weights = _scores(_BURIED), _weights(_BURIED)
        for dim in ("Clarity of contribution", "Rhetorical economy"):
            self.assertLessEqual(scores[dim], weights[dim] * 0.25)

    def test_no_critical_flag_is_used_to_force_the_failure(self) -> None:
        # The failure must come from the score, not from a flag — the whole
        # reason this paper slipped through the pre-#1047 rubric is that
        # nothing in it would make a reviewer stop reading.
        self.assertEqual(_summary_block(_BURIED, "Scores")["critical_flags"], [])


class TestBoldFixtureIsNotPenalizedForAmbition(unittest.TestCase):
    """Fixture B: at/above threshold with no overclaiming deduction."""

    def test_scores_at_or_above_the_advance_threshold(self) -> None:
        total = sum(_scores(_BOLD).values())
        self.assertGreaterEqual(
            total,
            _ADVANCE_THRESHOLD,
            "the bold-synthesis fixture must clear the >=35 gate — if it "
            "drops below, ambition has become costly and the 'Ambition is "
            "not novelty inflation' carve-out has regressed",
        )
        self.assertTrue(_summary_block(_BOLD, "Scores")["advance"])
        self.assertIn(
            "advance: true",
            (_review_dir(_BOLD) / "verdict.md").read_text(encoding="utf-8"),
        )

    def test_no_overclaiming_deduction_was_taken(self) -> None:
        block = _summary_block(_BOLD, "overclaiming_check")
        self.assertTrue(block["ran"])
        self.assertTrue(block["synthesis_claim_staked"])
        self.assertFalse(block["penalized_as_overclaiming"])
        self.assertFalse(block["unlabeled_conjecture_presented_as_result"])
        self.assertFalse(block["novelty_asserted_without_search"])
        self.assertEqual(
            sorted(block["ingredients_labelled"]),
            ["conjecture", "demonstrated", "derived", "synthesis"],
        )

    def test_no_underclaiming_finding_is_recorded(self) -> None:
        block = _summary_block(_BOLD, "underclaiming_check")
        self.assertTrue(block["ran"])
        self.assertIsNone(block["finding"])
        self.assertTrue(block["cold_reader"]["extractable_idea_matches_brief_strongest_claim"])
        prog = json.loads((_review_dir(_BOLD) / "_progress.json").read_text())
        self.assertEqual(prog["metadata"]["named_findings"], [])

    def test_the_body_labels_each_contribution_by_evidentiary_status(self) -> None:
        # The labelling is what earns the full dim 3 score without an
        # overclaiming deduction (rubric.md §"Ambition is not novelty
        # inflation"); if a future edit strips the labels, the recorded
        # verdict stops being justified.
        body = (_version_dir(_BOLD) / "main.tex").read_text(encoding="utf-8")
        for label in (
            r"\textbf{Demonstrated.}",
            r"\textbf{Derived.}",
            r"\textbf{Synthesis.}",
            r"\textbf{Conjecture.}",
        ):
            self.assertIn(label, body)

    def test_the_buried_fixture_does_not_carry_those_labels(self) -> None:
        body = (_version_dir(_BURIED) / "main.tex").read_text(encoding="utf-8")
        self.assertNotIn(r"\textbf{Conjecture.}", body)


class TestFixtureHygiene(unittest.TestCase):
    """Vendored-example trim guards, mirroring the sibling skills' tests."""

    def test_no_compiled_pdf_or_raster_is_vendored(self) -> None:
        for pattern in ("*.pdf", "*.png", "*.jpg"):
            leaked: List[Path] = list(_EXAMPLES.rglob(pattern))
            self.assertEqual(leaked, [], f"no {pattern} may be vendored: {leaked}")

    def test_examples_stay_within_the_size_envelope(self) -> None:
        # Sibling vendored examples run ~64-184 KB; two text-only fixtures
        # must stay in the same order of magnitude. A PDF leak would blow it.
        total = sum(p.stat().st_size for p in _EXAMPLES.rglob("*") if p.is_file())
        self.assertLess(
            total,
            300 * 1024,
            f"paper examples are {total // 1024} KB — expected < 300 KB",
        )

    def test_fixtures_declare_their_synthetic_provenance(self) -> None:
        # These papers report no real system and cite no real literature.
        # Every entry point a reader can land on must say so.
        readme = (_EXAMPLES / "README.md").read_text(encoding="utf-8")
        self.assertIn("synthetic", readme.lower())
        self.assertIn("Do not cite", readme)
        for fixture in (_BURIED, _BOLD):
            body = (_version_dir(fixture) / "main.tex").read_text(encoding="utf-8")
            self.assertIn("SYNTHETIC", body)
            bib = (_version_dir(fixture) / "refs.bib").read_text(encoding="utf-8")
            self.assertIn("INVENTED", bib)
            project_brief = (_project_dir(fixture) / "BRIEF.md").read_text(
                encoding="utf-8"
            )
            self.assertIn("synthetic", project_brief.lower())


if __name__ == "__main__":
    unittest.main()
