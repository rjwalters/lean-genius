"""Plan-shape tests for `--adopt-review` (issue #454 — Phase 3a of #432).

Stub paths are planned per sidecar; the original `review.md` is recorded
as PRESERVED, never as a rename source; the stub Review + provenance
marker build cleanly and carry the honest unscored-foreign shape (empty
scores/findings/flags, null total/threshold/verdict).
"""

from __future__ import annotations

from _fixtures import build_adopted_review_threads
from _project_migrate_skill_lib import adopt_review

build_adopt_review_plan = adopt_review.build_adopt_review_plan
build_stub_review = adopt_review.build_stub_review
build_provenance_marker = adopt_review.build_provenance_marker


class TestPlan:
    def test_no_rename_sources(self, tmp_path):
        # The plan carries StubConversion records, NOT renames — review.md
        # is never a rename source. The dataclass has no rename field at
        # all; this asserts the conversion records the preserved filename.
        project = build_adopted_review_threads(tmp_path)
        plan = build_adopt_review_plan(project)
        for c in plan.conversions:
            assert c.review_filename == "review.md"
            assert (c.sidecar_dir / "review.md").is_file()

    def test_stub_review_is_unscored_and_empty(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        plan = build_adopt_review_plan(project)
        conv = plan.conversions[0]
        stub = build_stub_review(conv)
        assert stub.unscored is True
        assert stub.scores == []
        assert stub.findings == []
        assert stub.critical_flags == []
        assert stub.total is None
        assert stub.threshold is None
        assert stub.verdict is None
        assert stub.version_dir == conv.version_dir
        assert stub.critic_id == conv.critic_id

    def test_stub_review_validates_against_schema(self, tmp_path):
        from anvil.lib.review_schema import Review

        project = build_adopted_review_threads(tmp_path)
        plan = build_adopt_review_plan(project)
        for conv in plan.conversions:
            stub = build_stub_review(conv)
            # Round-trip through the schema: dump → validate.
            reloaded = Review.model_validate_json(stub.model_dump_json())
            assert reloaded.unscored is True
            assert reloaded.scores == []

    def test_provenance_marker_shape(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        plan = build_adopt_review_plan(project)
        conv = plan.conversions[0]
        marker = build_provenance_marker(conv)
        assert marker == {
            "source": "foreign-adopted",
            "unscored": True,
            "origin_filename": "review.md",
            "adopted_by": "anvil:project-migrate#454",
        }

    def test_empty_plan_when_nothing_to_convert(self, tmp_path):
        project = build_adopted_review_threads(tmp_path, pre_converted=True)
        plan = build_adopt_review_plan(project)
        assert plan.is_noop
        assert plan.conversions == []
