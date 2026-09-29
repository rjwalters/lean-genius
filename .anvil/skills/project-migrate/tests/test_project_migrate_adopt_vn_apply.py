"""End-to-end apply tests for `--adopt-vn` (issue #432 Phase 1).

Covers: starter-BRIEF synthesis path (no enclosing BRIEF) and the
surgical-append path (operator BRIEF preserved byte-prefix), the strict
post-apply round-trip (`load_project_brief_strict` +
`discover_thread_root` on each adopted version dir — the #408
non-renamed-body path), git-mv history follow, and per-doc rollback on
an injected apply failure (tree restored byte-identical, no BRIEF
written).
"""

from __future__ import annotations

import subprocess

import pytest

from _fixtures import ENROLL_OPERATOR_BRIEF, build_vn_report_dirs
from _project_migrate_skill_lib import apply_mod, orchestrate
from anvil.lib.testing import tree_hash as _tree_digest

run_adopt_vn = orchestrate.run_adopt_vn


class TestAdoptNoBrief:
    def test_apply_renames_and_synthesizes_brief(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent

        result = run_adopt_vn(reports, apply=True)
        assert result.success, result.report

        # Version dirs + sidecars renamed in place.
        for n in (1, 2, 3, 5):
            assert (reports / f"reports.{n}" / "report.md").is_file()
            assert not (reports / f"v{n}").exists()
        for n in (3, 5):
            assert (
                reports / f"reports.{n}.review" / "review.md"
            ).is_file()
            assert not (reports / f"v{n}.review").exists()
        # Stray dir untouched.
        assert (reports / "notes-archive" / "scratch.md").is_file()
        # Bodies never renamed (the #408 carve-out).
        assert not (reports / "reports.3" / "reports.md").exists()

        # Starter BRIEF synthesized with the #408 TODO discipline.
        text = (project / "BRIEF.md").read_text(encoding="utf-8")
        assert "documents:" in text
        assert "slug: reports  # adopted-from: reports/vN" in text
        assert "artifact_type: report  # TODO(operator)" in text
        assert "# TODO(operator)" in text
        assert "## Enrollment log" in text
        assert "adopted vN report dirs" in text

    def test_strict_round_trip_and_discovery(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        from anvil.lib.project_brief import load_project_brief_strict
        from anvil.lib.project_discovery import discover_thread_root

        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent
        result = run_adopt_vn(reports, apply=True)
        assert result.success, result.report

        brief = load_project_brief_strict(project, validate_dirs=True)
        assert [d.slug for d in brief.documents] == ["reports"]
        assert brief.documents[0].artifact_type == "report"

        # AC: discover_thread_root resolves each adopted version dir
        # (the #408 non-renamed-body path).
        for n in (1, 2, 3, 5):
            discovery = discover_thread_root(reports / f"reports.{n}")
            assert discovery is not None
            assert discovery.slug == "reports"
            assert discovery.project_root == project

        assert "**Overall**: PASS" in result.report


class TestAdoptIntoExistingBrief:
    def test_apply_appends_surgically(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_project_brief=True)
        project = reports.parent

        result = run_adopt_vn(reports, apply=True)
        assert result.success, result.report

        new_text = (project / "BRIEF.md").read_text(encoding="utf-8")
        # Byte-identical operator frontmatter prefix preserved.
        original_fm_end = ENROLL_OPERATOR_BRIEF.index("\n---\n", 4)
        assert new_text.startswith(ENROLL_OPERATOR_BRIEF[:original_fm_end])
        assert "slug: reports  # adopted-from: reports/vN" in new_text
        assert (
            "Operator-authored prose that must survive byte-identically."
            in new_text
        )
        assert "## Enrollment log" in new_text

    def test_strict_round_trip_with_operator_brief(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        from anvil.lib.project_brief import load_project_brief_strict

        reports = build_vn_report_dirs(tmp_path, with_project_brief=True)
        result = run_adopt_vn(reports, apply=True)
        assert result.success, result.report

        brief = load_project_brief_strict(
            reports.parent, validate_dirs=True
        )
        assert [d.slug for d in brief.documents] == [
            "zeta-memo",
            "alpha-memo",
            "reports",
        ]
        # Operator fields survive the append.
        assert brief.theme == "sphere-brand"
        assert brief.documents[0].render_engine == "xelatex"


class TestSlugOverride:
    def test_apply_relocates_under_new_slug(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent
        result = run_adopt_vn(reports, slug="quarterly", apply=True)
        assert result.success, result.report
        for n in (1, 2, 3, 5):
            assert (
                project / "quarterly" / f"quarterly.{n}" / "report.md"
            ).is_file()
        assert (
            project / "quarterly" / "quarterly.3.review" / "review.md"
        ).is_file()
        # The family dir keeps its stray content only.
        assert (reports / "notes-archive").is_dir()
        assert not (reports / "v1").exists()


class TestGit:
    def _git(self, cwd, *args):
        return subprocess.run(
            ["git", *args],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=True,
        )

    def test_git_history_follows_adopted_dirs(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent
        self._git(project, "init", "-q")
        self._git(project, "config", "user.email", "t@example.com")
        self._git(project, "config", "user.name", "T")
        self._git(project, "add", "-A")
        self._git(project, "commit", "-q", "-m", "pre-adoption")

        result = run_adopt_vn(reports, apply=True)
        assert result.success, result.report
        assert result.apply_result.git_used

        status = self._git(project, "status", "--porcelain").stdout
        assert any(
            line.startswith("R") and "reports.3/report.md" in line
            for line in status.splitlines()
        ), status

        self._git(project, "add", "-A")
        self._git(project, "commit", "-q", "-m", "adopt")
        log = self._git(
            project,
            "log",
            "--follow",
            "--format=%s",
            "--",
            "reports/reports.3/report.md",
        ).stdout.splitlines()
        assert log == ["adopt", "pre-adoption"]


class TestRollback:
    def test_injected_failure_rolls_back_whole_family(
        self, tmp_path, monkeypatch
    ):
        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent
        before = _tree_digest(project)

        real_rename = apply_mod._rename

        def failing_rename(source, target, git_info):
            # Fail mid-family: earlier renames have already mutated
            # the tree, so the rollback path is genuinely exercised.
            if target.name == "reports.3":
                raise OSError("simulated rename failure")
            return real_rename(source, target, git_info)

        monkeypatch.setattr(apply_mod, "_rename", failing_rename)

        result = run_adopt_vn(reports, apply=True)
        assert not result.success
        assert result.apply_result is not None
        assert result.apply_result.failed_docs
        assert result.apply_result.failed_docs[0][0] == "reports"
        # No BRIEF written for a failed family (succeeded subset empty).
        assert not result.apply_result.brief_written
        assert not (project / "BRIEF.md").exists()
        # Tree restored byte-identical (per-doc snapshot rollback).
        assert _tree_digest(project) == before
