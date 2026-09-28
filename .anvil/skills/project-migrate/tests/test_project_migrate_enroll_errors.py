"""Plan-time hard-error tests for enrollment (issue #406).

Every refusal here fires BEFORE any mutation (two-phase batch
semantics): slug collisions (existing BRIEF, on-disk, intra-batch),
non-md/tex inputs, already-enrolled inputs (idempotency-as-refusal),
malformed existing BRIEFs, non-canonical --slug, multi-project batches,
and unmigrated-project guards.
"""

from __future__ import annotations

import pytest

from _fixtures import (
    build_loose_file_batch,
    build_loose_file_in_existing_project,
    build_loose_file_no_project,
)
from _project_migrate_skill_lib import enroll, orchestrate

EnrollError = enroll.EnrollError
build_enroll_plan = enroll.build_enroll_plan
run_enroll = orchestrate.run_enroll


def _tree_snapshot(root):
    return sorted(
        str(p.relative_to(root)) for p in root.rglob("*")
    )


class TestSlugCollisions:
    def test_collision_with_brief_slug_names_conflict(self, tmp_path):
        project_dir = build_loose_file_in_existing_project(
            tmp_path, loose_filename="zeta-memo.md"
        )
        with pytest.raises(EnrollError, match="zeta-memo"):
            build_enroll_plan([project_dir / "zeta-memo.md"])

    def test_collision_with_on_disk_dir(self, tmp_path):
        project_dir = build_loose_file_in_existing_project(tmp_path)
        # A stray dir (not a thread, not listed) with the derived name.
        (project_dir / "board-update").mkdir()
        with pytest.raises(EnrollError, match="board-update"):
            build_enroll_plan(
                [project_dir / "2026-05-19-board-update.md"]
            )

    def test_intra_batch_duplicate_slug(self, tmp_path):
        topical_dir = build_loose_file_batch(tmp_path)
        before = _tree_snapshot(topical_dir)
        with pytest.raises(EnrollError, match="same-topic"):
            build_enroll_plan(
                [
                    topical_dir / "2026-05-19-same-topic.md",
                    topical_dir / "same-topic-2026-05-20.md",
                ]
            )
        # Plan-time error → zero mutation.
        assert _tree_snapshot(topical_dir) == before


class TestInputRefusals:
    def test_non_md_tex_refused(self, tmp_path):
        topical_dir = build_loose_file_batch(tmp_path)
        with pytest.raises(EnrollError, match=r"\.md / \.tex"):
            build_enroll_plan([topical_dir / "notes.txt"])

    def test_missing_file_refused(self, tmp_path):
        with pytest.raises(EnrollError, match="not an existing file"):
            build_enroll_plan([tmp_path / "ghost.md"])

    def test_brief_and_readme_refused(self, tmp_path):
        project_dir = build_loose_file_in_existing_project(tmp_path)
        with pytest.raises(EnrollError, match="BRIEF.md"):
            build_enroll_plan([project_dir / "BRIEF.md"])
        readme = project_dir / "README.md"
        readme.write_text("# Readme\n", encoding="utf-8")
        with pytest.raises(EnrollError, match="README.md"):
            build_enroll_plan([readme])

    def test_batch_failure_aborts_whole_batch_pre_mutation(
        self, tmp_path
    ):
        topical_dir = build_loose_file_batch(tmp_path)
        before = _tree_snapshot(topical_dir)
        with pytest.raises(EnrollError):
            run_enroll(
                [
                    topical_dir / "2026-05-19-topic-a.md",
                    topical_dir / "notes.txt",
                ],
                apply=True,
            )
        assert _tree_snapshot(topical_dir) == before


class TestAlreadyEnrolled:
    def test_file_inside_version_dir_refused(self, tmp_path):
        project_dir = build_loose_file_in_existing_project(tmp_path)
        enrolled_body = (
            project_dir / "zeta-memo" / "zeta-memo.1" / "zeta-memo.md"
        )
        with pytest.raises(EnrollError, match="already"):
            build_enroll_plan([enrolled_body])

    def test_reenrolling_after_apply_is_refusal_not_duplicate(
        self, tmp_path
    ):
        project_dir = build_loose_file_in_existing_project(tmp_path)
        loose = project_dir / "2026-05-19-board-update.md"
        result = run_enroll([loose], apply=True)
        assert result.success, result.report
        body = (
            project_dir
            / "board-update"
            / "board-update.1"
            / "board-update.md"
        )
        with pytest.raises(EnrollError, match="already"):
            run_enroll([body], apply=True)

    def test_file_in_listed_thread_root_refused(self, tmp_path):
        pytest.importorskip("anvil.lib.project_discovery")
        project_dir = build_loose_file_in_existing_project(tmp_path)
        stray = project_dir / "zeta-memo" / "stray-notes.md"
        stray.write_text("# Stray\n", encoding="utf-8")
        with pytest.raises(EnrollError, match="already"):
            build_enroll_plan([stray])


class TestProjectResolution:
    def test_malformed_existing_brief_refused(self, tmp_path):
        topical_dir = build_loose_file_no_project(tmp_path)
        # A BRIEF.md that is NOT a parseable project BRIEF.
        (topical_dir / "BRIEF.md").write_text(
            "---\ncompany: acme\n---\n\n# Thread-level brief\n",
            encoding="utf-8",
        )
        with pytest.raises(EnrollError, match="parse"):
            build_enroll_plan([topical_dir / "2026-05-19-topic-a.md"])

    def test_unparseable_brief_yaml_refused(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        topical_dir = build_loose_file_no_project(tmp_path)
        (topical_dir / "BRIEF.md").write_text(
            "---\nproject: p\ndocuments:\n  - slug: x\n"
            "    artifact_type: not-a-real-type\n---\n",
            encoding="utf-8",
        )
        with pytest.raises(EnrollError, match="strict"):
            build_enroll_plan([topical_dir / "2026-05-19-topic-a.md"])

    def test_explicit_project_must_exist(self, tmp_path):
        topical_dir = build_loose_file_no_project(tmp_path)
        with pytest.raises(EnrollError, match="--project"):
            build_enroll_plan(
                [topical_dir / "2026-05-19-topic-a.md"],
                project=tmp_path / "nope",
            )

    def test_batch_spanning_projects_refused(self, tmp_path):
        dir_a = build_loose_file_no_project(tmp_path, dir_name="a")
        dir_b = build_loose_file_no_project(tmp_path, dir_name="b")
        with pytest.raises(EnrollError, match="multiple project roots"):
            build_enroll_plan(
                [
                    dir_a / "2026-05-19-topic-a.md",
                    dir_b / "topic-b-2026-05-19.md",
                ]
            )

    def test_unmigrated_thread_dirs_without_brief_refused(
        self, tmp_path
    ):
        topical_dir = build_loose_file_no_project(tmp_path)
        # A thread-shaped dir with no BRIEF anywhere: synthesis would
        # produce a BRIEF that fails validate_dirs. Refuse with the
        # project-migrate suggestion.
        (topical_dir / "old-thread" / "old-thread.1").mkdir(parents=True)
        with pytest.raises(EnrollError, match="project-migrate"):
            build_enroll_plan([topical_dir / "2026-05-19-topic-a.md"])


class TestFlagValidation:
    def test_slug_with_batch_refused(self, tmp_path):
        topical_dir = build_loose_file_no_project(tmp_path)
        with pytest.raises(EnrollError, match="--slug"):
            build_enroll_plan(
                [
                    topical_dir / "2026-05-19-topic-a.md",
                    topical_dir / "topic-b-2026-05-19.md",
                ],
                slug="one-slug",
            )

    def test_non_canonical_slug_refused(self, tmp_path):
        topical_dir = build_loose_file_no_project(tmp_path)
        with pytest.raises(EnrollError, match="not canonical"):
            build_enroll_plan(
                [topical_dir / "2026-05-19-topic-a.md"],
                slug="Topic_A",
            )

    def test_unknown_artifact_type_refused(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        topical_dir = build_loose_file_no_project(tmp_path)
        with pytest.raises(EnrollError, match="artifact"):
            build_enroll_plan(
                [topical_dir / "2026-05-19-topic-a.md"],
                artifact_type="not-a-real-type",
            )

    def test_empty_file_list_refused(self):
        with pytest.raises(EnrollError, match="No files"):
            build_enroll_plan([])
