"""Paper-skill coverage for audience fit + operator feedback (issue #1322).

Reproduces the reported defect on a temp ``paper`` thread: a BRIEF declaring
a mathematical audience, and a v4 ``main.tex`` whose body and appendix still
carry governance notes addressed to the project's operator and bare
repo-relative artifact paths. It then checks that

- the deterministic pre-flight (``anvil/lib/audience_check.py``, wired at
  ``paper-review`` step 4i) flags both classes, ``major`` in the body and
  ``minor`` in the appendix, while staying ADVISORY: a passing content review
  alongside the ``.audience/`` sidecar still ADVANCEs;
- the operator-feedback path (``anvil/lib/operator_feedback.py``, wired at
  ``paper-revise`` step 4) reopens a READY thread: with no ``.operator/``
  sibling the step-4 pre-check exits (READY); with a blocking operator flag
  it requires another revision and the aggregate verdict is BLOCK;
- the four documents name the new rules (doc-coverage guards).

Distinct filename per the #58 packaging convention.
"""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[4]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from anvil.lib.audience_check import (  # noqa: E402
    RULE_GOVERNANCE,
    RULE_UNLINKED_PATH,
    check_audience,
    write_review_dir,
)
from anvil.lib.critics import aggregate, compute_verdict, load_review  # noqa: E402
from anvil.lib.operator_feedback import (  # noqa: E402
    BRIEF_AMENDMENT_FLAG_TYPE,
    build_operator_review,
    revise_required_by_operator,
    write_operator_review,
)
from anvil.lib.review_schema import CriticalFlag, Kind, Review, Score, Verdict  # noqa: E402

_SKILL_ROOT = Path(__file__).resolve().parent.parent

_BRIEF = """---
audience: Combinatorialists and formal-methods readers
---
# erdos-drop

The campaign-process sections may be shortened or moved to appendices.
"""

_MAIN_TEX = r"""\documentclass{anvil-paper}
\begin{document}
\section{Cost to verify}
No replay wave is authorized by this estimate.
\section{Artifacts and receipts}
Everything lives at \url{https://github.com/example/proofs}.
Census timing: \texttt{refs/CENSUS\_TIMING\_20260928.md}.
Solver timing: \texttt{sat49/H1\_V3\_SOLVER\_TIMING\_20260916.md}.
\appendix
\section{Process}
Operator goal \#25 made the outline the allocation instrument.
\end{document}
"""


def _passing_review(version_dir: str, total: int = 37) -> Review:
    return Review(
        schema_version="1",
        kind=Kind.JUDGMENT,
        version_dir=version_dir,
        critic_id="review",
        scores=[Score(dimension="content", score=total, max=44, justification="READY at v4.")],
        findings=[],
        critical_flags=[],
    )


class _ThreadCase(unittest.TestCase):
    def setUp(self):
        self._td = tempfile.TemporaryDirectory()
        thread = Path(self._td.name) / "erdos-drop"
        self.version = thread / "erdos-drop.4"
        self.version.mkdir(parents=True)
        (thread / "BRIEF.md").write_text(_BRIEF, encoding="utf-8")
        (self.version / "main.tex").write_text(_MAIN_TEX, encoding="utf-8")

    def tearDown(self):
        self._td.cleanup()


class TestReportedDefectIsFlagged(_ThreadCase):
    def test_governance_body_major_appendix_minor(self):
        result = check_audience(self.version)
        gov = [h for h in result.active_hits if h.rule == RULE_GOVERNANCE]
        self.assertEqual([(h.line, h.severity) for h in gov], [(4, "major"), (11, "minor")])
        self.assertEqual(result.declared_audience, ["Combinatorialists and formal-methods readers"])

    def test_bare_artifact_paths_flagged_with_public_repo_fix(self):
        result = check_audience(self.version)
        paths = [h for h in result.active_hits if h.rule == RULE_UNLINKED_PATH]
        self.assertEqual(
            [h.terms for h in paths],
            [("refs/CENSUS_TIMING_20260928.md",), ("sat49/H1_V3_SOLVER_TIMING_20260916.md",)],
        )
        self.assertEqual(result.public_repo_url, "https://github.com/example/proofs")

    def test_audience_sidecar_is_advisory(self):
        out = write_review_dir(self.version, check_audience(self.version))
        audience = load_review(out.parent)
        self.assertEqual(audience.critical_flags, [])
        agg = aggregate([_passing_review(self.version.name), audience])
        self.assertEqual(agg.total, 37)
        self.assertEqual(compute_verdict(agg, threshold=35), Verdict.ADVANCE)


class TestOperatorFeedbackReopensReady(_ThreadCase):
    def test_no_operator_sibling_keeps_ready(self):
        self.assertFalse(revise_required_by_operator(self.version))
        agg = aggregate([_passing_review(self.version.name)])
        self.assertEqual(compute_verdict(agg, threshold=35), Verdict.ADVANCE)

    def test_operator_flag_requires_revision(self):
        flag = CriticalFlag(
            type=BRIEF_AMENDMENT_FLAG_TYPE,
            justification="BRIEF now forbids process notes in the published text.",
        )
        out = write_operator_review(self.version, build_operator_review(self.version.name, [flag]))
        self.assertTrue(revise_required_by_operator(self.version))
        operator = load_review(out)
        self.assertEqual(operator.kind, Kind.JUDGMENT)
        self.assertEqual(operator.critic_id, "operator")
        self.assertEqual(operator.verdict, Verdict.BLOCK)
        agg = aggregate([_passing_review(self.version.name), operator])
        self.assertEqual(agg.total, 37)
        self.assertEqual(compute_verdict(agg, threshold=35), Verdict.BLOCK)


def _read(rel: str) -> str:
    return (_SKILL_ROOT / rel).read_text(encoding="utf-8")


class TestDocCoverage(unittest.TestCase):
    def test_rubric_names_audience_fit_sub_rule(self):
        text = _read("rubric.md")
        self.assertIn("## Audience fit (dims 7 and 9) — issue #1322", text)
        self.assertIn("`major` in the body, `minor` in an appendix", text)
        self.assertIn("delete the sentence or move it to a non-published process log", text)
        self.assertIn("anvil/lib/audience_check.py", text)

    def test_paper_review_runs_audience_preflight(self):
        text = _read("commands/paper-review.md")
        self.assertIn("4i. **Run audience-fit pre-flight", text)
        self.assertIn("python -m anvil.lib.audience_check <thread>.{N}/ --write-review", text)
        self.assertIn("<thread>.{N}.audience/_review.json", text)
        self.assertIn("**Audience fit (D7 / D9) — issue #1322**", text)

    def test_paper_audit_link_hygiene(self):
        text = _read("commands/paper-audit.md")
        self.assertIn("6c. **Artifact link hygiene", text)
        self.assertIn("public_repo_url", text)
        self.assertIn("**Unlinked artifact path**", text)

    def test_paper_revise_step4_consults_operator_sibling(self):
        text = _read("commands/paper-revise.md")
        step4 = text[text.index("4. **Verdict pre-check**"):text.index("5. **Initialize `_progress.json`**")]
        self.assertIn("<thread>.{N}.operator/", step4)
        self.assertIn("python -m anvil.lib.operator_feedback check", step4)
        self.assertIn('critic_id: "operator"', step4)
        step3 = text[text.index("3. **Iteration cap check**"):text.index("4. **Verdict pre-check**")]
        self.assertIn("operator_override", step3)
        self.assertIn("BRIEF amendment made after READY", step3)

    def test_skill_documents_operator_path_and_public_repo_url(self):
        text = _read("SKILL.md")
        self.assertIn("**Operator feedback after READY (issue #1322).**", text)
        self.assertIn('`critic_id: "operator"`', text)
        self.assertIn("`kind: judgment`", text)
        self.assertIn("| `public_repo_url` | string |", text)
        ready_row = next(ln for ln in text.splitlines() if ln.startswith("| `READY` |"))
        self.assertIn(".operator/", ready_row)


if __name__ == "__main__":
    unittest.main()
