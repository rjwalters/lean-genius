"""Apply tests for `--adopt-review` (issue #454 — Phase 3a of #432).

`_review.json` + `_meta.json` written via `staged_sidecar`; `review.md`
byte-identical pre/post (hash compare); rollback on an injected mid-write
failure leaves the dir untouched.
"""

from __future__ import annotations

import hashlib
import json

import pytest

from anvil.lib.testing import tree_hash as _tree_digest
from _fixtures import FOREIGN_REVIEW_PROSE, build_adopted_review_threads
from _project_migrate_skill_lib import adopt_review, orchestrate

run_adopt_review = orchestrate.run_adopt_review


def _digest(path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class TestApply:
    def test_writes_stub_and_marker_preserves_review(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)

        # Record review.md digests before apply.
        before = {}
        for p in project.rglob("review.md"):
            before[p.relative_to(project)] = _digest(p)

        result = run_adopt_review(project, apply=True)
        assert result.success, result.report
        assert sorted(result.apply_result.converted) == [
            "meridian-a.2.review",
            "meridian-c.5.review",
            "meridian-c.7.enablement",
            "meridian-c.7.s101",
        ]

        for sidecar_rel in (
            "meridian-c/meridian-c.7.enablement",
            "meridian-a/meridian-a.2.review",
        ):
            sidecar = project / sidecar_rel
            # The two additive files exist.
            assert (sidecar / "_review.json").is_file()
            assert (sidecar / "_meta.json").is_file()
            # review.md preserved byte-identical.
            assert (sidecar / "review.md").read_text() == FOREIGN_REVIEW_PROSE

            review = json.loads((sidecar / "_review.json").read_text())
            assert review["unscored"] is True
            assert review["scores"] == []
            assert review["total"] is None
            assert review["verdict"] is None

            marker = json.loads((sidecar / "_meta.json").read_text())
            assert marker["source"] == "foreign-adopted"
            assert marker["unscored"] is True

        # Every review.md unchanged (hash compare).
        for p in project.rglob("review.md"):
            assert before[p.relative_to(project)] == _digest(p)

    def test_stub_uses_staged_sidecar(self, tmp_path, monkeypatch):
        # Assert the apply path routes through anvil.lib.sidecar.staged_sidecar
        # (the required critic-sibling write primitive).
        import anvil.lib.sidecar as sidecar_mod

        calls = []
        real = sidecar_mod.staged_sidecar

        def spy(final_dir, required_files, **kw):
            calls.append((final_dir.name, list(required_files)))
            return real(final_dir, required_files, **kw)

        monkeypatch.setattr(adopt_review, "staged_sidecar", spy)

        project = build_adopted_review_threads(tmp_path)
        result = run_adopt_review(project, apply=True)
        assert result.success, result.report
        # One staged_sidecar call per converted sidecar.
        assert len(calls) == 4
        for _name, required in calls:
            assert "review.md" in required
            assert "_review.json" in required
            assert "_meta.json" in required

    def test_no_leftover_staging_dirs(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        run_adopt_review(project, apply=True)
        # No leading-dot .tmp / .bak dirs survive a clean apply.
        leftovers = [
            p.name
            for p in project.rglob("*")
            if p.is_dir()
            and p.name.startswith(".")
            and (p.name.endswith(".tmp") or p.name.endswith(".bak"))
        ]
        assert leftovers == []


class TestRollback:
    def test_injected_failure_restores_dir_byte_identical(
        self, tmp_path, monkeypatch
    ):
        project = build_adopted_review_threads(tmp_path)

        # Fail mid-write INSIDE the staged_sidecar body for ONE sidecar
        # (after the live dir has been moved aside to its .bak backup), so
        # the restore-from-backup path is genuinely exercised.
        import anvil.lib.sidecar as sidecar_mod

        real = sidecar_mod.staged_sidecar

        def failing_staged(final_dir, required_files, **kw):
            cm = real(final_dir, required_files, **kw)
            if final_dir.name == "meridian-c.7.s101":
                # Enter (creating the staging dir + moving aside already
                # happened in _convert_one), then raise in-body.
                class _Boom:
                    def __enter__(self_inner):
                        staging = cm.__enter__()
                        raise RuntimeError("simulated mid-write failure")

                    def __exit__(self_inner, *a):
                        return cm.__exit__(*a)

                return _Boom()
            return cm

        monkeypatch.setattr(adopt_review, "staged_sidecar", failing_staged)

        result = run_adopt_review(project, apply=True)
        assert not result.success, result.report
        assert result.apply_result is not None
        failed = {n for n, _ in result.apply_result.failed}
        assert "meridian-c.7.s101" in failed

        # The failed sidecar is restored byte-identical: still review.md
        # only, no partial _review.json / _meta.json.
        s101 = project / "meridian-c" / "meridian-c.7.s101"
        assert s101.is_dir()
        assert (s101 / "review.md").read_text() == FOREIGN_REVIEW_PROSE
        assert not (s101 / "_review.json").exists()
        assert not (s101 / "_meta.json").exists()
        # No staging / backup dirs left behind.
        assert not (
            project / "meridian-c" / ".meridian-c.7.s101.tmp"
        ).exists()
        assert not (
            project / "meridian-c" / ".meridian-c.7.s101.bak"
        ).exists()

    def test_total_failure_leaves_tree_untouched(
        self, tmp_path, monkeypatch
    ):
        project = build_adopted_review_threads(tmp_path)
        before = _tree_digest(project)

        def always_fail(conv):
            raise RuntimeError("simulated failure")

        monkeypatch.setattr(adopt_review, "build_stub_review", always_fail)

        result = run_adopt_review(project, apply=True)
        assert not result.success
        assert result.apply_result.converted == []
        # Whole tree byte-identical — every conversion rolled back.
        assert _tree_digest(project) == before
