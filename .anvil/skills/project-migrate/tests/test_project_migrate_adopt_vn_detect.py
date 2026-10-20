"""vN family detection tests for `--adopt-vn` (issue #432 Phase 1).

Covers: family grouping (version gaps tolerated), minor-versioned
oddball refusal with suggested targets, versioned-tag refusal, stray
non-versioned dirs + orphan sidecars reported-untouched, no-family
no-op, and the `Shape.ADOPT_VN` plan-mode-only regression lock
(`detect_shape` / `_classify` never return it).
"""

from __future__ import annotations

import pytest

from _fixtures import build_vn_report_dirs
from _project_migrate_skill_lib import adopt_vn, detect

build_adopt_vn_plan = adopt_vn.build_adopt_vn_plan
AdoptVnError = adopt_vn.AdoptVnError
Shape = detect.Shape


class TestFamilyGrouping:
    def test_versions_grouped_with_gap_tolerated(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        plan = build_adopt_vn_plan(reports)
        assert len(plan.documents) == 1
        doc = plan.documents[0]
        version_targets = sorted(
            r.target.name
            for r in doc.renames
            if r.target.name.split(".")[-1].isdigit()
        )
        assert version_targets == [
            "reports.1",
            "reports.2",
            "reports.3",
            "reports.5",
        ]
        assert any("Version gaps tolerated" in n for n in doc.notes)
        assert any("v4" in n for n in doc.notes if "gap" in n.lower())

    def test_sidecars_grouped_with_their_version(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        plan = build_adopt_vn_plan(reports)
        sidecar_targets = sorted(
            r.target.name
            for r in plan.documents[0].renames
            if not r.target.name.split(".")[-1].isdigit()
        )
        assert sidecar_targets == ["reports.3.review", "reports.5.review"]

    def test_v0_adopts(self, tmp_path):
        reports = build_vn_report_dirs(
            tmp_path, versions=(0, 1), review_versions=()
        )
        plan = build_adopt_vn_plan(reports)
        names = {r.target.name for r in plan.documents[0].renames}
        assert names == {"reports.0", "reports.1"}

    def test_single_version_family(self, tmp_path):
        reports = build_vn_report_dirs(
            tmp_path, versions=(7,), review_versions=()
        )
        plan = build_adopt_vn_plan(reports)
        assert [r.target.name for r in plan.documents[0].renames] == [
            "reports.7"
        ]


class TestRefusals:
    def test_minor_versioned_oddball_refuses_pre_mutation(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_minor=True)
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports)
        msg = str(excinfo.value)
        assert "v14.1" in msg
        # Suggested manual target: next free integer after max(1,2,3,5).
        assert "v6" in msg
        assert "Nothing was modified" in msg

    def test_multiple_minors_get_distinct_suggestions(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_minor=True)
        (reports / "v2.3").mkdir()
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports)
        msg = str(excinfo.value)
        assert "v14.1" in msg and "v2.3" in msg
        assert "v6" in msg and "v7" in msg

    def test_versioned_sidecar_tag_refuses(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        (reports / "v3.review-v2").mkdir()
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports)
        msg = str(excinfo.value)
        assert "v3.review-v2" in msg
        assert "Phase 2" in msg

    def test_missing_directory_refuses(self, tmp_path):
        with pytest.raises(AdoptVnError):
            build_adopt_vn_plan(tmp_path / "does-not-exist")


class TestStraysAndOrphans:
    def test_stray_dir_untouched_and_reported(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        plan = build_adopt_vn_plan(reports)
        doc = plan.documents[0]
        sources = {r.source.name for r in doc.renames}
        assert "notes-archive" not in sources
        assert any("notes-archive" in n for n in doc.notes)

    def test_orphan_sidecar_untouched_and_reported(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        (reports / "v9.review").mkdir()
        plan = build_adopt_vn_plan(reports)
        doc = plan.documents[0]
        sources = {r.source.name for r in doc.renames}
        assert "v9.review" not in sources
        assert any("v9.review" in n for n in doc.notes)

    def test_loose_files_in_family_dir_untouched(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        (reports / "index.md").write_text("# index\n", encoding="utf-8")
        plan = build_adopt_vn_plan(reports)
        sources = {r.source.name for r in plan.documents[0].renames}
        assert "index.md" not in sources


class TestNoFamilyNoOp:
    def test_empty_dir_is_noop_plan(self, tmp_path):
        empty = tmp_path / "proj" / "reports"
        empty.mkdir(parents=True)
        plan = build_adopt_vn_plan(empty)
        assert plan.documents == []
        assert plan.is_noop

    def test_already_adopted_tree_is_noop_plan(self, tmp_path):
        adopted = tmp_path / "proj" / "reports"
        (adopted / "reports.1").mkdir(parents=True)
        (adopted / "reports.1" / "report.md").write_text(
            "# r\n", encoding="utf-8"
        )
        plan = build_adopt_vn_plan(adopted)
        assert plan.documents == []
        assert plan.is_noop


class TestShapeIsPlanModeOnly:
    """AC: `Shape.ADOPT_VN` is a plan-mode tag only — `_classify`
    behavior is unchanged (regression-locked)."""

    def test_member_exists_with_stable_value(self):
        assert Shape.ADOPT_VN.value == "adopt_vn"

    def test_plan_is_stamped_adopt_vn(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        plan = build_adopt_vn_plan(reports)
        assert plan.shape is Shape.ADOPT_VN

    def test_detect_shape_never_returns_adopt_vn(self, tmp_path):
        # The vN family dir itself, its project root, and an adopted
        # tree: detect_shape classifies through the unchanged
        # _classify path and never returns the plan-mode tags.
        reports = build_vn_report_dirs(tmp_path)
        for target in (reports, reports.parent):
            shape = detect.detect_shape(target)
            assert shape is not Shape.ADOPT_VN
            assert shape is not Shape.ENROLL

    def test_classify_untouched_on_known_fixtures(self, tmp_path):
        # Characterization lock on a canonical fixture: a fully
        # migrated project still classifies FULLY_MIGRATED.
        from _fixtures import build_fully_migrated

        project = build_fully_migrated(tmp_path)
        assert detect.detect_shape(project) is Shape.FULLY_MIGRATED
