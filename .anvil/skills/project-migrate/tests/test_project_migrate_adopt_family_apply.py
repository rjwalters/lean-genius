"""End-to-end apply tests for `--adopt-family` (issue #440).

Covers: multi-family adoption with sidecar renames per the tag map
(starter-BRIEF synthesis path and the surgical-append path), the
strict post-apply round-trip (`load_project_brief_strict` +
`discover_thread_root` on each adopted version dir), git-mv history
follow, and per-doc rollback on an injected apply failure (the failed
family's tree restored byte-identical; the BRIEF written for the
succeeded subset — the enroll contract).
"""

from __future__ import annotations

import subprocess

import pytest

from _fixtures import (
    DEFAULT_TAG_MAP,
    ENROLL_OPERATOR_BRIEF,
    build_letter_family_threads,
    write_tag_map,
)
from _project_migrate_skill_lib import apply_mod, orchestrate
from anvil.lib.testing import tree_hash as _tree_digest

run_adopt_family = orchestrate.run_adopt_family

ARTIFACT_TYPE = "ip-uspto-provisional"


def _tag_map(tmp_path):
    return write_tag_map(tmp_path / "tag-map.json", DEFAULT_TAG_MAP)


class TestAdoptNoBrief:
    def test_apply_renames_and_synthesizes_brief(self, tmp_path):
        project = build_letter_family_threads(tmp_path)

        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert result.success, result.report

        # Version dirs relocated under their derived slug dirs.
        for slug, versions in (
            ("meridian-a", (1, 2)),
            ("meridian-c", (5, 7)),
        ):
            for n in versions:
                assert (
                    project / slug / f"{slug}.{n}" / "spec.md"
                ).is_file()
        assert not (project / "Meridian.A.1").exists()
        assert not (project / "Meridian.C.7").exists()

        # Sidecars renamed per the tag map (incl. the review-v2 remap).
        assert (
            project / "meridian-a" / "meridian-a.2.review" / "review.md"
        ).is_file()
        assert (
            project / "meridian-c" / "meridian-c.5.review" / "review.md"
        ).is_file()
        assert (
            project / "meridian-c" / "meridian-c.7.audit2" / "review.md"
        ).is_file()
        assert not (project / "Meridian.C.5.review-v2").exists()

        # Strays + orphan sidecars untouched.
        assert (project / "notes-archive" / "scratch.md").is_file()
        assert (project / "Meridian.C.9.fto" / "review.md").is_file()
        assert (project / "Meridian.C.7.1" / "oddball.md").is_file()

        # Bodies never renamed (the #408 carve-out).
        assert not (
            project / "meridian-c" / "meridian-c.7" / "meridian-c.md"
        ).exists()

        # Starter BRIEF synthesized with the TODO discipline.
        text = (project / "BRIEF.md").read_text(encoding="utf-8")
        assert "documents:" in text
        assert "slug: meridian-a  # adopted-from: Meridian.A.{N}" in text
        assert (
            "artifact_type: ip-uspto-provisional  # TODO(operator): "
            "confirm — applied invocation-wide by --adopt-family" in text
        )
        assert "## Enrollment log" in text
        assert "adopted letter family `Meridian.C`" in text

    def test_strict_round_trip_and_discovery(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        from anvil.lib.project_brief import load_project_brief_strict
        from anvil.lib.project_discovery import discover_thread_root

        project = build_letter_family_threads(tmp_path)
        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert result.success, result.report

        brief = load_project_brief_strict(project, validate_dirs=True)
        assert [d.slug for d in brief.documents] == [
            "meridian-a",
            "meridian-c",
        ]
        for doc in brief.documents:
            assert doc.artifact_type == ARTIFACT_TYPE

        # AC: discover_thread_root resolves each adopted version dir
        # (the #408 non-renamed-body path).
        for slug, versions in (
            ("meridian-a", (1, 2)),
            ("meridian-c", (5, 7)),
        ):
            for n in versions:
                discovery = discover_thread_root(
                    project / slug / f"{slug}.{n}"
                )
                assert discovery is not None
                assert discovery.slug == slug
                assert discovery.project_root == project

        assert "**Overall**: PASS" in result.report


class TestAdoptIntoExistingBrief:
    def test_apply_appends_surgically(self, tmp_path):
        project = build_letter_family_threads(
            tmp_path, with_project_brief=True
        )

        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type="ip-uspto",
            apply=True,
        )
        assert result.success, result.report

        new_text = (project / "BRIEF.md").read_text(encoding="utf-8")
        # Byte-identical operator frontmatter prefix preserved.
        original_fm_end = ENROLL_OPERATOR_BRIEF.index("\n---\n", 4)
        assert new_text.startswith(ENROLL_OPERATOR_BRIEF[:original_fm_end])
        assert "slug: meridian-a  # adopted-from: Meridian.A.{N}" in new_text
        assert "artifact_type: ip-uspto  # TODO(operator)" in new_text
        assert (
            "Operator-authored prose that must survive byte-identically."
            in new_text
        )
        assert "## Enrollment log" in new_text

    def test_strict_round_trip_with_operator_brief(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        from anvil.lib.project_brief import load_project_brief_strict

        project = build_letter_family_threads(
            tmp_path, with_project_brief=True
        )
        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type="ip-uspto",
            apply=True,
        )
        assert result.success, result.report

        brief = load_project_brief_strict(project, validate_dirs=True)
        assert [d.slug for d in brief.documents] == [
            "zeta-memo",
            "alpha-memo",
            "meridian-a",
            "meridian-c",
        ]
        # Operator fields survive the append.
        assert brief.theme == "sphere-brand"
        assert brief.documents[0].render_engine == "xelatex"


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
        project = build_letter_family_threads(tmp_path)
        self._git(project, "init", "-q")
        self._git(project, "config", "user.email", "t@example.com")
        self._git(project, "config", "user.name", "T")
        self._git(project, "add", "-A")
        self._git(project, "commit", "-q", "-m", "pre-adoption")

        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert result.success, result.report
        assert result.apply_result.git_used

        status = self._git(project, "status", "--porcelain").stdout
        assert any(
            line.startswith("R") and "meridian-c.7/spec.md" in line
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
            "meridian-c/meridian-c.7/spec.md",
        ).stdout.splitlines()
        assert log == ["adopt", "pre-adoption"]


class TestRollback:
    def test_injected_failure_isolates_per_family(
        self, tmp_path, monkeypatch
    ):
        # Fail mid-way through the SECOND family (`meridian-c`):
        # `meridian-a` stays applied, `meridian-c` is rolled back
        # byte-identical, and the BRIEF is written for the succeeded
        # subset (the enroll contract routed through Shape.ADOPT_FAMILY).
        project = build_letter_family_threads(tmp_path)
        family_c_dirs = sorted(
            d.name for d in project.iterdir() if d.name.startswith(
                "Meridian.C."
            )
        )

        real_rename = apply_mod._rename

        def failing_rename(source, target, git_info):
            if target.name == "meridian-c.7":
                raise OSError("simulated rename failure")
            return real_rename(source, target, git_info)

        monkeypatch.setattr(apply_mod, "_rename", failing_rename)

        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert not result.success
        assert result.apply_result is not None
        assert result.apply_result.applied_docs == ["meridian-a"]
        assert [s for s, _ in result.apply_result.failed_docs] == [
            "meridian-c"
        ]

        # meridian-a applied for real.
        assert (
            project / "meridian-a" / "meridian-a.2.review" / "review.md"
        ).is_file()
        # meridian-c restored: every original dir back, target gone.
        for name in family_c_dirs:
            assert (project / name).is_dir(), name
        assert not (project / "meridian-c").exists()

        # BRIEF written for the succeeded subset only.
        assert result.apply_result.brief_written
        text = (project / "BRIEF.md").read_text(encoding="utf-8")
        assert "slug: meridian-a" in text
        assert "slug: meridian-c" not in text

    def test_first_family_failure_restores_it_byte_identical(
        self, tmp_path, monkeypatch
    ):
        project = build_letter_family_threads(tmp_path)

        real_rename = apply_mod._rename

        def failing_rename(source, target, git_info):
            # Fail mid-family so earlier renames already mutated the
            # tree and the rollback path is genuinely exercised.
            if target.name == "meridian-a.2":
                raise OSError("simulated rename failure")
            return real_rename(source, target, git_info)

        monkeypatch.setattr(apply_mod, "_rename", failing_rename)

        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert not result.success
        failed = {s for s, _ in result.apply_result.failed_docs}
        assert "meridian-a" in failed
        # meridian-c (the other family) still applied + listed; the
        # failed family's subtree is restored.
        for name in ("Meridian.A.1", "Meridian.A.2", "Meridian.A.2.review"):
            assert (project / name).is_dir(), name
        assert not (project / "meridian-a").exists()

    def test_whole_batch_failure_leaves_tree_untouched(
        self, tmp_path, monkeypatch
    ):
        project = build_letter_family_threads(tmp_path)
        before = _tree_digest(project)

        def always_failing_rename(source, target, git_info):
            raise OSError("simulated rename failure")

        monkeypatch.setattr(apply_mod, "_rename", always_failing_rename)

        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert not result.success
        assert not result.apply_result.brief_written
        assert not (project / "BRIEF.md").exists()
        assert _tree_digest(project) == before
