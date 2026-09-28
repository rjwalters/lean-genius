"""Tests for the dangling-citation lint in `anvil:project-share` (issue #758).

The exporter's `verify` step checks layout, never content — a thread
body can cite a project-root working document (or any repo-relative
file) that is not part of the export set, and the recipient gets a
dangling pointer. This lint scans plan-collected markdown for such
citations and reports (never blocks) findings in the run summary and
`EXPORT.md`.
"""

from __future__ import annotations

import sys
import unittest
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_share_skill_lib import citations, config as config_mod  # noqa: E402
from _project_share_skill_lib import orchestrate, plan as plan_mod  # noqa: E402
from _share_fixtures import (  # noqa: E402
    build_full_project,
    build_project_with_dangling_citation,
)

from anvil.lib.project_brief import load_project_brief_strict  # noqa: E402

NOW = datetime(2026, 7, 28, 12, 0, 0, tzinfo=timezone.utc)


def _plan_for(project: Path) -> plan_mod.SharePlan:
    cfg = config_mod.ExportConfig()
    brief = load_project_brief_strict(project)
    return plan_mod.build_plan(project, brief, cfg)


class TestFindDanglingCitations(unittest.TestCase):
    def test_bare_filename_and_link_both_flagged(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_dangling_citation(Path(td))
            share_plan = _plan_for(project)
            result = citations.find_dangling_citations(share_plan)

            self.assertFalse(result.ok)
            resolved = {f.resolved_rel for f in result.findings}
            self.assertEqual(resolved, {"STRATEGIC-OPTIONS.md"})

            slugs = {f.doc_slug for f in result.findings}
            self.assertEqual(slugs, {"investment-memo", "kill-thresholds"})

            citation_texts = {f.citation_text for f in result.findings}
            self.assertIn("STRATEGIC-OPTIONS.md", citation_texts)
            self.assertIn("../../STRATEGIC-OPTIONS.md", citation_texts)

    def test_nonexistent_bare_filename_not_flagged(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_dangling_citation(Path(td))
            share_plan = _plan_for(project)
            result = citations.find_dangling_citations(share_plan)
            texts = {f.citation_text for f in result.findings}
            self.assertNotIn("not-a-real-file.md", texts)

    def test_link_to_exported_sibling_doc_not_flagged(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_dangling_citation(Path(td))
            share_plan = _plan_for(project)
            result = citations.find_dangling_citations(share_plan)
            resolved = {f.resolved_rel for f in result.findings}
            self.assertNotIn(
                "investment-memo/investment-memo.1/investment-memo.md",
                resolved,
            )

    def test_clean_project_has_no_findings(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            share_plan = _plan_for(project)
            result = citations.find_dangling_citations(share_plan)
            self.assertTrue(result.ok, result.findings)


class TestOrchestrateSurfacesFindings(unittest.TestCase):
    def test_dry_run_report_carries_finding(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_dangling_citation(Path(td))
            result = orchestrate.run(project, dry_run=True, now=NOW)
            self.assertIsNotNone(result.citation_result)
            assert result.citation_result is not None
            self.assertFalse(result.citation_result.ok)
            self.assertIn("STRATEGIC-OPTIONS.md", result.report)
            self.assertIn("## Citations", result.report)

    def test_apply_report_and_export_md_carry_finding(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_dangling_citation(Path(td))
            result = orchestrate.run(project, now=NOW)
            # Report-only: does not affect success.
            self.assertTrue(result.success, result.report)
            self.assertIn("STRATEGIC-OPTIONS.md", result.report)

            export_text = (project / "SHARE" / "EXPORT.md").read_text(
                encoding="utf-8"
            )
            self.assertIn("## Citations", export_text)
            self.assertIn("STRATEGIC-OPTIONS.md", export_text)

    def test_clean_project_export_md_has_no_citations_section(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            result = orchestrate.run(project, now=NOW)
            self.assertTrue(result.success, result.report)
            export_text = (project / "SHARE" / "EXPORT.md").read_text(
                encoding="utf-8"
            )
            self.assertNotIn("## Citations", export_text)


if __name__ == "__main__":
    unittest.main()
