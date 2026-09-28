"""End-to-end enrollment tests (issue #406).

Covers: enroll-into-existing-project (file moved, BRIEF byte-prefix
preserved, strict parse passes, ``discover_thread_root`` resolves),
enroll-with-no-project (minimal BRIEF synthesized via the #408 path),
batch enrollment, ``.tex`` enrollment (slug-echo body + paper inference),
git-mv history follow, and apply-time per-doc failure isolation with
the BRIEF written for the succeeded subset.
"""

from __future__ import annotations

import subprocess

import pytest

from _fixtures import (
    ENROLL_OPERATOR_BRIEF,
    build_loose_file_batch,
    build_loose_file_in_existing_project,
    build_loose_file_no_project,
)
from _project_migrate_skill_lib import apply_mod, orchestrate

run_enroll = orchestrate.run_enroll


class TestEnrollIntoExistingProject:
    def test_apply_moves_file_and_appends_brief(self, tmp_path):
        project_dir = build_loose_file_in_existing_project(tmp_path)
        loose = project_dir / "2026-05-19-board-update.md"

        result = run_enroll([loose], apply=True)

        assert result.success, result.report
        # File moved to the canonical thread shape.
        body = (
            project_dir
            / "board-update"
            / "board-update.1"
            / "board-update.md"
        )
        assert body.is_file()
        assert not loose.exists()
        assert "Loose memo awaiting enrollment." in body.read_text(
            encoding="utf-8"
        )

        # BRIEF: byte-identical frontmatter prefix + appended entry.
        new_text = (project_dir / "BRIEF.md").read_text(encoding="utf-8")
        original_fm_end = ENROLL_OPERATOR_BRIEF.index("\n---\n", 4)
        assert new_text.startswith(ENROLL_OPERATOR_BRIEF[:original_fm_end])
        assert (
            "  - slug: board-update  # enrolled-from: "
            "2026-05-19-board-update.md (date: 2026-05-19)" in new_text
        )
        # Body prose preserved + enrollment log appended.
        assert (
            "Operator-authored prose that must survive byte-identically."
            in new_text
        )
        assert "## Enrollment log" in new_text
        assert "source date: 2026-05-19" in new_text

    def test_strict_parse_and_discovery_after_apply(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        from anvil.lib.project_brief import load_project_brief_strict
        from anvil.lib.project_discovery import discover_thread_root

        project_dir = build_loose_file_in_existing_project(tmp_path)
        loose = project_dir / "2026-05-19-board-update.md"
        result = run_enroll([loose], apply=True)
        assert result.success, result.report

        brief = load_project_brief_strict(project_dir, validate_dirs=True)
        assert [d.slug for d in brief.documents] == [
            "zeta-memo",
            "alpha-memo",
            "board-update",
        ]
        # Operator fields preserved through the append.
        assert brief.theme == "sphere-brand"
        assert brief.documents[0].render_engine == "xelatex"

        body = (
            project_dir
            / "board-update"
            / "board-update.1"
            / "board-update.md"
        )
        discovery = discover_thread_root(body)
        assert discovery is not None
        assert discovery.slug == "board-update"
        assert discovery.project_root == project_dir

    def test_explicit_slug_and_artifact_type(self, tmp_path):
        project_dir = build_loose_file_in_existing_project(tmp_path)
        loose = project_dir / "2026-05-19-board-update.md"
        result = run_enroll(
            [loose],
            slug="q2-board-letter",
            artifact_type="position-paper",
            apply=True,
        )
        assert result.success, result.report
        assert (
            project_dir
            / "q2-board-letter"
            / "q2-board-letter.1"
            / "q2-board-letter.md"
        ).is_file()
        new_text = (project_dir / "BRIEF.md").read_text(encoding="utf-8")
        assert "slug: q2-board-letter" in new_text
        # Explicit type → no inference, no TODO marker on the new entry.
        entry_start = new_text.index("slug: q2-board-letter")
        entry_text = new_text[entry_start:]
        assert "artifact_type: position-paper" in entry_text
        assert "TODO(operator)" not in entry_text.split("---")[0]


class TestEnrollNoProject:
    def test_brief_synthesized_with_todo_markers(self, tmp_path):
        topical_dir = build_loose_file_no_project(tmp_path)
        loose = topical_dir / "2026-05-19-topic-a.md"

        result = run_enroll([loose], apply=True)
        assert result.success, result.report

        brief_path = topical_dir / "BRIEF.md"
        assert brief_path.is_file()
        text = brief_path.read_text(encoding="utf-8")
        assert "documents:" in text
        assert (
            "  - slug: topic-a  # enrolled-from: 2026-05-19-topic-a.md "
            "(date: 2026-05-19)" in text
        )
        # #408 TODO-marker discipline on the synthesized BRIEF.
        assert "# TODO(operator)" in text
        assert "## Enrollment log" in text
        assert (
            topical_dir / "topic-a" / "topic-a.1" / "topic-a.md"
        ).is_file()

    def test_synthesized_brief_round_trips(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        from anvil.lib.project_brief import load_project_brief_strict
        from anvil.lib.project_discovery import discover_thread_root

        topical_dir = build_loose_file_no_project(tmp_path)
        result = run_enroll(
            [topical_dir / "topic-b-2026-05-19.md"], apply=True
        )
        assert result.success, result.report
        brief = load_project_brief_strict(topical_dir, validate_dirs=True)
        assert [d.slug for d in brief.documents] == ["topic-b"]
        discovery = discover_thread_root(
            topical_dir / "topic-b" / "topic-b.1" / "topic-b.md"
        )
        assert discovery is not None
        assert discovery.slug == "topic-b"

    def test_explicit_project_dir(self, tmp_path):
        topical_dir = build_loose_file_no_project(tmp_path)
        target_project = tmp_path / "elsewhere"
        target_project.mkdir()
        result = run_enroll(
            [topical_dir / "2026-05-19-topic-a.md"],
            project=target_project,
            apply=True,
        )
        assert result.success, result.report
        assert (
            target_project / "topic-a" / "topic-a.1" / "topic-a.md"
        ).is_file()
        assert (target_project / "BRIEF.md").is_file()


class TestEnrollBatch:
    def test_batch_enrolls_n_files_one_brief(self, tmp_path):
        topical_dir = build_loose_file_batch(tmp_path)
        files = [
            topical_dir / "2026-05-19-topic-a.md",
            topical_dir / "draft-response-2026-05-19.md",
            topical_dir / "whitepaper.tex",
        ]
        result = run_enroll(files, apply=True)
        assert result.success, result.report
        assert len(result.plan.documents) == 3

        assert (
            topical_dir / "topic-a" / "topic-a.1" / "topic-a.md"
        ).is_file()
        assert (
            topical_dir
            / "draft-response"
            / "draft-response.1"
            / "draft-response.md"
        ).is_file()
        # .tex body slug-echoes (no external-tooling carve-out for
        # new enrollments).
        assert (
            topical_dir / "whitepaper" / "whitepaper.1" / "whitepaper.tex"
        ).is_file()

        text = (topical_dir / "BRIEF.md").read_text(encoding="utf-8")
        assert "slug: topic-a" in text
        assert "slug: draft-response" in text
        assert "slug: whitepaper" in text
        # \documentclass{article} → paper inference, TODO-marked.
        assert "artifact_type: paper" in text

    def test_apply_failure_isolates_per_doc_brief_for_succeeded_subset(
        self, tmp_path, monkeypatch
    ):
        topical_dir = build_loose_file_batch(tmp_path)
        files = [
            topical_dir / "2026-05-19-topic-a.md",
            topical_dir / "draft-response-2026-05-19.md",
        ]

        real_rename = apply_mod._rename

        def failing_rename(source, target, git_info):
            if "draft-response" in str(target):
                raise OSError("simulated rename failure")
            return real_rename(source, target, git_info)

        monkeypatch.setattr(apply_mod, "_rename", failing_rename)

        result = run_enroll(files, apply=True)
        # Overall run fails (a doc failed) ...
        assert not result.success
        assert result.apply_result is not None
        assert result.apply_result.applied_docs == ["topic-a"]
        assert len(result.apply_result.failed_docs) == 1
        assert result.apply_result.failed_docs[0][0] == "draft-response"

        # ... but the succeeded doc IS enrolled and listed.
        assert result.apply_result.brief_written
        text = (topical_dir / "BRIEF.md").read_text(encoding="utf-8")
        assert "slug: topic-a" in text
        assert "slug: draft-response" not in text
        # The failed file was rolled back to its loose location.
        assert (topical_dir / "draft-response-2026-05-19.md").is_file()
        assert not (topical_dir / "draft-response").exists()


class TestEnrollTex:
    def test_proposal_documentclass_infers_proposal(self, tmp_path):
        topical_dir = tmp_path / "proposals"
        topical_dir.mkdir()
        tex = topical_dir / "gossamer-bid-2026-05-19.tex"
        tex.write_text(
            "\\documentclass{anvil-proposal}\n"
            "\\begin{document}\nBid.\n\\end{document}\n",
            encoding="utf-8",
        )
        result = run_enroll([tex], apply=True)
        assert result.success, result.report
        assert (
            topical_dir
            / "gossamer-bid"
            / "gossamer-bid.1"
            / "gossamer-bid.tex"
        ).is_file()
        text = (topical_dir / "BRIEF.md").read_text(encoding="utf-8")
        assert "artifact_type: proposal" in text
        assert "# TODO(operator)" in text

    def test_tex_rename_note_emitted(self, tmp_path):
        topical_dir = build_loose_file_batch(tmp_path)
        result = run_enroll([topical_dir / "whitepaper.tex"])
        assert any(
            "not rewritten" in note.lower() or "NOT rewritten" in note
            for doc in result.plan.documents
            for note in doc.notes
        )
        assert "whitepaper.tex" in result.report


class TestEnrollGit:
    def _git(self, cwd, *args):
        return subprocess.run(
            ["git", *args],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=True,
        )

    def test_git_history_follows_enrolled_file(self, tmp_path):
        project_dir = build_loose_file_in_existing_project(tmp_path)
        self._git(project_dir, "init", "-q")
        self._git(project_dir, "config", "user.email", "t@example.com")
        self._git(project_dir, "config", "user.name", "T")
        self._git(project_dir, "add", "-A")
        self._git(project_dir, "commit", "-q", "-m", "pre-enrollment")

        loose = project_dir / "2026-05-19-board-update.md"
        result = run_enroll([loose], apply=True)
        assert result.success, result.report
        assert result.apply_result.git_used

        # The move is staged as a rename (git mv was used).
        status = self._git(
            project_dir, "status", "--porcelain"
        ).stdout
        assert any(
            line.startswith("R") and "board-update.md" in line
            for line in status.splitlines()
        ), status

        # And history follows across a commit boundary.
        self._git(project_dir, "add", "-A")
        self._git(project_dir, "commit", "-q", "-m", "enroll")
        log = self._git(
            project_dir,
            "log",
            "--follow",
            "--format=%s",
            "--",
            "board-update/board-update.1/board-update.md",
        ).stdout.splitlines()
        assert log == ["enroll", "pre-enrollment"]
