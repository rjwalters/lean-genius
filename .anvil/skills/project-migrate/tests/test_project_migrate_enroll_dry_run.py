"""Dry-run contract tests for enrollment (issue #406).

Dry-run is the universal default (``apply=False``): the run must leave
the tree byte-identical (digest check) while the report carries the
full proposed BRIEF — rendered through the SAME code path the apply
step writes, so the preview equals the eventual write byte-for-byte.
"""

from __future__ import annotations


from _fixtures import (
    build_loose_file_in_existing_project,
    build_loose_file_no_project,
)
from _project_migrate_skill_lib import orchestrate
from anvil.lib.testing import tree_hash as _tree_digest

run_enroll = orchestrate.run_enroll


class TestEnrollDryRun:
    def test_dry_run_is_default_and_mutates_nothing(self, tmp_path):
        project_dir = build_loose_file_in_existing_project(tmp_path)
        before = _tree_digest(project_dir)

        result = run_enroll(
            [project_dir / "2026-05-19-board-update.md"]
        )

        assert result.success
        assert result.apply_result is None
        assert _tree_digest(project_dir) == before

    def test_dry_run_no_project_mutates_nothing(self, tmp_path):
        topical_dir = build_loose_file_no_project(tmp_path)
        before = _tree_digest(topical_dir)
        result = run_enroll([topical_dir / "2026-05-19-topic-a.md"])
        assert result.success
        assert _tree_digest(topical_dir) == before

    def test_dry_run_report_previews_full_brief(self, tmp_path):
        # No-project case: AC 5 — dry-run prints the full proposed
        # BRIEF (synthesized via render_project_brief).
        topical_dir = build_loose_file_no_project(tmp_path)
        result = run_enroll([topical_dir / "2026-05-19-topic-a.md"])
        assert "## Proposed `BRIEF.md`" in result.report
        assert "documents:" in result.report
        assert "slug: topic-a" in result.report
        assert "# TODO(operator)" in result.report
        assert "synthesized" in result.report

    def test_dry_run_preview_matches_apply_write(self, tmp_path):
        # Byte-identity between the previewed BRIEF and what --apply
        # writes (the shared render_enroll_brief code path).
        project_dir = build_loose_file_in_existing_project(tmp_path)
        loose = project_dir / "2026-05-19-board-update.md"

        preview = run_enroll([loose])
        fence_start = preview.report.index("````markdown\n") + len(
            "````markdown\n"
        )
        fence_end = preview.report.index("\n````", fence_start)
        previewed_brief = preview.report[fence_start:fence_end]

        applied = run_enroll([loose], apply=True)
        assert applied.success, applied.report
        written = (project_dir / "BRIEF.md").read_text(encoding="utf-8")
        assert written.rstrip("\n") == previewed_brief.rstrip("\n")
