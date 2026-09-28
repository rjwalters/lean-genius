"""Dry-run contract tests for `--adopt-vn` (issue #432 Phase 1).

Dry-run is the universal default (``apply=False``): the run must leave
the tree byte-identical (digest check) while the report carries the
full proposed BRIEF — rendered through the SAME ``render_enroll_brief``
code path the apply step writes, so the preview equals the eventual
write byte-for-byte (both the synthesis and the surgical-append
variants).
"""

from __future__ import annotations


import pytest

from _fixtures import build_vn_report_dirs
from _project_migrate_skill_lib import adopt_vn, orchestrate
from anvil.lib.testing import tree_hash as _tree_digest

run_adopt_vn = orchestrate.run_adopt_vn
AdoptVnError = adopt_vn.AdoptVnError


def _previewed_brief(report: str) -> str:
    fence_start = report.index("````markdown\n") + len("````markdown\n")
    fence_end = report.index("\n````", fence_start)
    return report[fence_start:fence_end]


class TestAdoptVnDryRun:
    def test_dry_run_is_default_and_mutates_nothing(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent
        before = _tree_digest(project)

        result = run_adopt_vn(reports)

        assert result.success
        assert result.apply_result is None
        assert _tree_digest(project) == before

    def test_dry_run_with_existing_brief_mutates_nothing(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_project_brief=True)
        project = reports.parent
        before = _tree_digest(project)
        result = run_adopt_vn(reports)
        assert result.success
        assert _tree_digest(project) == before

    def test_noop_run_mutates_nothing_even_under_apply(self, tmp_path):
        empty = tmp_path / "proj" / "reports"
        empty.mkdir(parents=True)
        before = _tree_digest(tmp_path)
        result = run_adopt_vn(empty, apply=True)
        assert result.success
        assert result.apply_result is None
        assert "nothing to adopt" in result.report
        assert _tree_digest(tmp_path) == before

    def test_preview_matches_apply_write_synthesis(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent

        preview = run_adopt_vn(reports)
        previewed = _previewed_brief(preview.report)

        applied = run_adopt_vn(reports, apply=True)
        assert applied.success, applied.report
        written = (project / "BRIEF.md").read_text(encoding="utf-8")
        assert written.rstrip("\n") == previewed.rstrip("\n")

    def test_preview_matches_apply_write_append(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_project_brief=True)
        project = reports.parent

        preview = run_adopt_vn(reports)
        previewed = _previewed_brief(preview.report)

        applied = run_adopt_vn(reports, apply=True)
        assert applied.success, applied.report
        written = (project / "BRIEF.md").read_text(encoding="utf-8")
        assert written.rstrip("\n") == previewed.rstrip("\n")

    def test_leading_zero_refusal_mutates_nothing_even_under_apply(
        self, tmp_path
    ):
        # Issue #458: the v07/v7 slot collision refuses at scan time —
        # the tree must stay byte-identical even with apply=True.
        reports = build_vn_report_dirs(tmp_path, with_leading_zero_dup=True)
        project = reports.parent
        before = _tree_digest(project)
        with pytest.raises(AdoptVnError):
            run_adopt_vn(reports, apply=True)
        assert _tree_digest(project) == before

    def test_duplicate_sidecar_slot_refusal_mutates_nothing_under_apply(
        self, tmp_path
    ):
        # Issue #458: v03.review + v3.review (single v3/) previously
        # planned two renames to ONE target and failed MID-APPLY,
        # post-mutation. Now: plan-time refusal, tree untouched.
        reports = build_vn_report_dirs(tmp_path)
        dup = reports / "v03.review"
        dup.mkdir()
        (dup / "review.md").write_text("# dup\n", encoding="utf-8")
        project = reports.parent
        before = _tree_digest(project)
        with pytest.raises(AdoptVnError):
            run_adopt_vn(reports, apply=True)
        assert _tree_digest(project) == before
