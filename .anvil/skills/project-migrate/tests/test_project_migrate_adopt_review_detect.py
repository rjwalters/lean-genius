"""Detection tests for `--adopt-review` (issue #454 — Phase 3a of #432).

The pure planner finds `review.md`-only critic sidecars under an
already-adopted tree, ignores already-converted siblings
(`_review.json`-present), ignores real reviews, and ignores version dirs
and bodies.
"""

from __future__ import annotations

import pytest

from _fixtures import build_adopted_review_threads
from _project_migrate_skill_lib import adopt_review

build_adopt_review_plan = adopt_review.build_adopt_review_plan
AdoptReviewError = adopt_review.AdoptReviewError


def _names(plan):
    return sorted(c.sidecar_dir.name for c in plan.conversions)


class TestDetect:
    def test_finds_review_md_only_sidecars(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        plan = build_adopt_review_plan(project)
        # Every foreign sidecar (review.md only) is a conversion target.
        assert _names(plan) == [
            "meridian-a.2.review",
            "meridian-c.5.review",
            "meridian-c.7.enablement",
            "meridian-c.7.s101",
        ]
        assert not plan.is_noop

    def test_infers_version_dir_and_critic_id(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        plan = build_adopt_review_plan(project)
        by_name = {c.sidecar_dir.name: c for c in plan.conversions}
        c = by_name["meridian-c.7.enablement"]
        assert c.version_dir == "meridian-c.7"
        assert c.critic_id == "enablement"
        assert c.review_filename == "review.md"

    def test_ignores_already_converted(self, tmp_path):
        # Every sidecar already carries a stub _review.json — nothing to do.
        project = build_adopted_review_threads(tmp_path, pre_converted=True)
        plan = build_adopt_review_plan(project)
        assert plan.conversions == []
        assert plan.is_noop
        # Each is reported as skipped (already recognizable).
        skipped_reasons = {name: reason for name, reason in plan.skipped}
        assert "meridian-c.7.s101" in skipped_reasons
        assert "recognizable" in skipped_reasons["meridian-c.7.s101"]

    def test_ignores_real_scored_sibling(self, tmp_path):
        # The genuinely-scored .audit sibling carries a _review.json — it
        # passes _has_recognizable_review and is never a conversion target.
        project = build_adopted_review_threads(
            tmp_path, with_real_sibling=True
        )
        plan = build_adopt_review_plan(project)
        assert "meridian-c.7.audit" not in _names(plan)
        # But the foreign review.md-only siblings on the same version dir
        # ARE still found.
        assert "meridian-c.7.enablement" in _names(plan)
        assert "meridian-c.7.s101" in _names(plan)

    def test_does_not_treat_version_dirs_as_sidecars(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        plan = build_adopt_review_plan(project)
        # `meridian-c.7` is a version dir (tag would be a bare digit) — never
        # a sidecar.
        for c in plan.conversions:
            assert not c.sidecar_dir.name[len(c.version_dir) + 1:].isdigit()
            assert "spec.md" not in [
                p.name for p in c.sidecar_dir.iterdir()
            ] or (c.sidecar_dir / "review.md").is_file()

    def test_missing_directory_raises(self, tmp_path):
        with pytest.raises(AdoptReviewError):
            build_adopt_review_plan(tmp_path / "does-not-exist")

    def test_thread_root_passed_directly(self, tmp_path):
        # Passing a single thread root (not the project root) also works.
        project = build_adopted_review_threads(tmp_path)
        plan = build_adopt_review_plan(project / "meridian-a")
        assert _names(plan) == ["meridian-a.2.review"]
