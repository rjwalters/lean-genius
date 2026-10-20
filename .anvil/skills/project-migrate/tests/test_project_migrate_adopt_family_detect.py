"""Letter-family detection tests for `--adopt-family` (issue #440).

Covers: family grouping by ``{Project}.{Letter}`` stem (version gaps
tolerated), sidecar grouping with their version dir, strays + orphan
sidecars excluded-and-reported (including the numeric-tag
``Meridian.C.7.1`` corner that matches neither grammar), no-family
no-op, and the `Shape.ADOPT_FAMILY` plan-mode-only regression lock
(`detect_shape` / `_classify` never return it).
"""

from __future__ import annotations

import pytest

from _fixtures import (
    DEFAULT_TAG_MAP,
    build_letter_family_threads,
    write_tag_map,
)
from _project_migrate_skill_lib import adopt_family, detect

build_adopt_family_plan = adopt_family.build_adopt_family_plan
AdoptFamilyError = adopt_family.AdoptFamilyError
Shape = detect.Shape

ARTIFACT_TYPE = "ip-uspto-provisional"


def _plan(project, tmp_path, **kwargs):
    tag_map = write_tag_map(tmp_path / "tag-map.json", DEFAULT_TAG_MAP)
    kwargs.setdefault("tag_map_path", tag_map)
    kwargs.setdefault("artifact_type", ARTIFACT_TYPE)
    return build_adopt_family_plan(project, **kwargs)


class TestFamilyGrouping:
    def test_families_grouped_by_letter_stem(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = _plan(project, tmp_path)
        assert [d.slug for d in plan.documents] == [
            "meridian-a",
            "meridian-c",
        ]

    def test_version_gap_tolerated(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = _plan(project, tmp_path)
        doc_c = plan.documents[1]
        version_targets = sorted(
            r.target.name
            for r in doc_c.renames
            if r.target.name.split(".")[-1].isdigit()
        )
        assert version_targets == ["meridian-c.5", "meridian-c.7"]
        assert any("Version gaps tolerated" in n for n in doc_c.notes)
        assert any(
            "Meridian.C.6" in n for n in doc_c.notes if "gap" in n.lower()
        )

    def test_sidecars_grouped_with_their_version(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = _plan(project, tmp_path)
        doc_a = plan.documents[0]
        sidecar_targets = sorted(
            r.target.name
            for r in doc_a.renames
            if not r.target.name.split(".")[-1].isdigit()
        )
        assert sidecar_targets == ["meridian-a.2.review"]

    def test_single_family_single_version(self, tmp_path):
        project = tmp_path / "solo"
        (project / "Solo.B.4").mkdir(parents=True)
        (project / "Solo.B.4" / "spec.md").write_text(
            "# s\n", encoding="utf-8"
        )
        plan = build_adopt_family_plan(
            project, artifact_type=ARTIFACT_TYPE
        )
        assert [d.slug for d in plan.documents] == ["solo-b"]
        assert [r.target.name for r in plan.documents[0].renames] == [
            "solo-b.4"
        ]


class TestStraysAndOrphans:
    def test_stray_dirs_untouched_and_reported(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = _plan(project, tmp_path)
        sources = {
            r.source.name for d in plan.documents for r in d.renames
        }
        assert "notes-archive" not in sources
        strays = plan.family_strays
        assert "notes-archive" in strays

    def test_numeric_tag_dir_is_stray_not_sidecar(self, tmp_path):
        # `Meridian.C.7.1` matches neither the version grammar (the
        # letter position holds a digit) nor the sidecar grammar (tags
        # start with a non-digit) — stray, untouched, reported.
        project = build_letter_family_threads(tmp_path)
        plan = _plan(project, tmp_path)
        sources = {
            r.source.name for d in plan.documents for r in d.renames
        }
        assert "Meridian.C.7.1" not in sources
        assert "Meridian.C.7.1" in plan.family_strays

    def test_orphan_sidecar_untouched_and_reported_on_family(
        self, tmp_path
    ):
        project = build_letter_family_threads(tmp_path)
        plan = _plan(project, tmp_path)
        sources = {
            r.source.name for d in plan.documents for r in d.renames
        }
        assert "Meridian.C.9.fto" not in sources
        doc_c = plan.documents[1]
        assert any("Meridian.C.9.fto" in n for n in doc_c.notes)

    def test_sidecar_of_unknown_stem_is_stray(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        (project / "Ghost.Z.1.review").mkdir()
        plan = _plan(project, tmp_path)
        assert "Ghost.Z.1.review" in plan.family_strays

    def test_loose_files_untouched(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        (project / "index.md").write_text("# index\n", encoding="utf-8")
        plan = _plan(project, tmp_path)
        sources = {
            r.source.name for d in plan.documents for r in d.renames
        }
        assert "index.md" not in sources


class TestNoFamilyNoOp:
    def test_empty_dir_is_noop_plan(self, tmp_path):
        empty = tmp_path / "proj"
        empty.mkdir(parents=True)
        plan = build_adopt_family_plan(empty)
        assert plan.documents == []
        assert plan.is_noop

    def test_already_adopted_tree_is_noop_plan(self, tmp_path):
        adopted = tmp_path / "proj"
        (adopted / "meridian-c" / "meridian-c.7").mkdir(parents=True)
        (adopted / "meridian-c" / "meridian-c.7" / "spec.md").write_text(
            "# s\n", encoding="utf-8"
        )
        plan = build_adopt_family_plan(adopted)
        assert plan.documents == []
        assert plan.is_noop

    def test_missing_directory_refuses(self, tmp_path):
        with pytest.raises(AdoptFamilyError):
            build_adopt_family_plan(tmp_path / "does-not-exist")


class TestShapeIsPlanModeOnly:
    """AC: `Shape.ADOPT_FAMILY` is a plan-mode tag only — `_classify`
    behavior is unchanged (regression-locked)."""

    def test_member_exists_with_stable_value(self):
        assert Shape.ADOPT_FAMILY.value == "adopt_family"

    def test_plan_is_stamped_adopt_family(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = _plan(project, tmp_path)
        assert plan.shape is Shape.ADOPT_FAMILY

    def test_detect_shape_never_returns_adopt_family(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        for target in (project, project.parent):
            shape = detect.detect_shape(target)
            assert shape is not Shape.ADOPT_FAMILY
            assert shape is not Shape.ADOPT_VN
            assert shape is not Shape.ENROLL

    def test_classify_untouched_on_known_fixtures(self, tmp_path):
        # Characterization lock on a canonical fixture: a fully
        # migrated project still classifies FULLY_MIGRATED.
        from _fixtures import build_fully_migrated

        project = build_fully_migrated(tmp_path)
        assert detect.detect_shape(project) is Shape.FULLY_MIGRATED
