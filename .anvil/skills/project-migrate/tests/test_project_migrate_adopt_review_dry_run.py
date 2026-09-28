"""Dry-run tests for `--adopt-review` (issue #454 — Phase 3a of #432).

Dry-run is the default and leaves the input tree byte-identical
(snapshot-and-diff, the adopt-vn / adopt-family precedent). The report
names every planned conversion without writing anything.
"""

from __future__ import annotations


from _fixtures import build_adopted_review_threads
from _project_migrate_skill_lib import orchestrate
from anvil.lib.testing import tree_hash as _tree_digest

run_adopt_review = orchestrate.run_adopt_review


class TestDryRun:
    def test_default_is_dry_run_zero_mutation(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        before = _tree_digest(project)

        result = run_adopt_review(project)  # no apply= → dry-run
        assert result.success
        assert result.apply_result is None

        # Not a single byte changed.
        assert _tree_digest(project) == before
        # No stub files written anywhere.
        assert list(project.rglob("_review.json")) == []
        assert list(project.rglob("_meta.json")) == []

    def test_report_lists_conversions(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        result = run_adopt_review(project)
        report = result.report
        assert "Phase 3a" in report
        assert "NO LLM" in report
        assert "meridian-c.7.enablement" in report
        assert "meridian-a.2.review" in report
        # The stub field set is described.
        assert "unscored" in report
        assert "foreign-provenance" in report or "foreign-adopted" in report
        assert "byte-identical" in report

    def test_explicit_apply_false_is_dry_run(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        before = _tree_digest(project)
        run_adopt_review(project, apply=False)
        assert _tree_digest(project) == before
