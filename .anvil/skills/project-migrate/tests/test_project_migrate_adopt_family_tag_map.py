"""Declarative `--tag-map` contract tests for `--adopt-family` (issue #440).

The binding spec is the issue #432 curation comment ("Declarative
tag-mapping contract"), pinned verbatim by the #440 curation. Covers
the four refusal classes (missing map when sidecars exist; unmapped
observed tag — listing the tags; value violating the canonical tag
grammar; two foreign tags → one canonical tag on the SAME version dir),
the legal shapes (identity mappings, `review-v2` remap, the same
colliding pair on DIFFERENT version dirs, sidecar-free families with no
map), and the file-shape refusals. Every refusal is plan-time —
nothing is mutated.
"""

from __future__ import annotations

import json

import pytest

from _fixtures import (
    DEFAULT_TAG_MAP,
    build_letter_family_threads,
    write_tag_map,
)
from _project_migrate_skill_lib import adopt_family
from anvil.lib.testing import tree_hash as _tree_digest

build_adopt_family_plan = adopt_family.build_adopt_family_plan
load_tag_map = adopt_family.load_tag_map
AdoptFamilyError = adopt_family.AdoptFamilyError

ARTIFACT_TYPE = "ip-uspto-provisional"


class TestFileShape:
    def test_missing_file_refuses(self, tmp_path):
        with pytest.raises(AdoptFamilyError) as excinfo:
            load_tag_map(tmp_path / "nope.json")
        assert "Cannot read" in str(excinfo.value)

    def test_invalid_json_refuses(self, tmp_path):
        path = tmp_path / "tag-map.json"
        path.write_text("{not json", encoding="utf-8")
        with pytest.raises(AdoptFamilyError) as excinfo:
            load_tag_map(path)
        assert "not valid JSON" in str(excinfo.value)

    def test_missing_tag_map_key_refuses(self, tmp_path):
        path = tmp_path / "tag-map.json"
        path.write_text(json.dumps({"map": {}}), encoding="utf-8")
        with pytest.raises(AdoptFamilyError) as excinfo:
            load_tag_map(path)
        assert "tag_map" in str(excinfo.value)

    def test_non_string_entry_refuses(self, tmp_path):
        path = tmp_path / "tag-map.json"
        path.write_text(
            json.dumps({"tag_map": {"review": 3}}), encoding="utf-8"
        )
        with pytest.raises(AdoptFamilyError) as excinfo:
            load_tag_map(path)
        assert "string" in str(excinfo.value)

    def test_identity_map_loads(self, tmp_path):
        path = write_tag_map(tmp_path / "tag-map.json", DEFAULT_TAG_MAP)
        assert load_tag_map(path) == DEFAULT_TAG_MAP


class TestMissingMapRefusal:
    def test_sidecars_without_tag_map_refused_listing_observed(
        self, tmp_path
    ):
        project = build_letter_family_threads(tmp_path)
        before = _tree_digest(project)
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(project, artifact_type=ARTIFACT_TYPE)
        msg = str(excinfo.value)
        assert "--tag-map" in msg
        # The full observed vocabulary is listed (orphan sidecars are
        # untouched, so `fto` is NOT required).
        for tag in (
            "review",
            "review-v2",
            "pre_flight",
            "enablement",
            "s101",
            "audit",
            "audit2",
        ):
            assert f"`{tag}`" in msg
        assert "`fto`" not in msg
        assert _tree_digest(project) == before

    def test_sidecar_free_family_needs_no_tag_map(self, tmp_path):
        project = build_letter_family_threads(
            tmp_path, with_sidecars=False
        )
        plan = build_adopt_family_plan(
            project, artifact_type=ARTIFACT_TYPE
        )
        assert [d.slug for d in plan.documents] == [
            "meridian-a",
            "meridian-c",
        ]
        assert plan.tag_resolution == []


class TestUnmappedTagRefusal:
    def test_incomplete_map_refused_listing_missing_tags(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        incomplete = {
            k: v
            for k, v in DEFAULT_TAG_MAP.items()
            if k not in ("s101", "pre_flight")
        }
        tag_map = write_tag_map(tmp_path / "tag-map.json", incomplete)
        before = _tree_digest(project)
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=tag_map,
                artifact_type=ARTIFACT_TYPE,
            )
        msg = str(excinfo.value)
        assert "Unmapped" in msg
        assert "`pre_flight`" in msg and "`s101`" in msg
        # Mapped tags are NOT listed as missing.
        assert "`review-v2`" not in msg
        assert _tree_digest(project) == before

    def test_extra_unobserved_entries_are_allowed(self, tmp_path):
        # One map can serve many directories — entries for tags not
        # observed here are harmless.
        project = build_letter_family_threads(tmp_path)
        mapping = dict(DEFAULT_TAG_MAP, fto="fto", critic="critic")
        tag_map = write_tag_map(tmp_path / "tag-map.json", mapping)
        plan = build_adopt_family_plan(
            project, tag_map_path=tag_map, artifact_type=ARTIFACT_TYPE
        )
        assert len(plan.documents) == 2


class TestValueGrammarRefusal:
    @pytest.mark.parametrize(
        "bad_value", ["review-v2", "re.view", "audit-v3", "1review", ""]
    )
    def test_non_canonical_value_refused(self, tmp_path, bad_value):
        project = build_letter_family_threads(tmp_path)
        mapping = dict(DEFAULT_TAG_MAP)
        mapping["review-v2"] = bad_value
        tag_map = write_tag_map(tmp_path / "tag-map.json", mapping)
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=tag_map,
                artifact_type=ARTIFACT_TYPE,
            )
        msg = str(excinfo.value)
        assert "non-canonical" in msg
        assert "review-v2" in msg


class TestSameDirCollision:
    def test_two_tags_to_one_canonical_on_same_dir_refused(
        self, tmp_path
    ):
        # `.audit` + `.audit2` coexist on `Meridian.C.7` — mapping both
        # to `audit` collides.
        project = build_letter_family_threads(tmp_path)
        mapping = dict(DEFAULT_TAG_MAP, audit2="audit")
        tag_map = write_tag_map(tmp_path / "tag-map.json", mapping)
        before = _tree_digest(project)
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=tag_map,
                artifact_type=ARTIFACT_TYPE,
            )
        msg = str(excinfo.value)
        assert "Meridian.C.7" in msg
        assert "`audit`" in msg
        assert "audit2" in msg
        assert _tree_digest(project) == before

    def test_same_pair_on_different_dirs_accepted(self, tmp_path):
        # DEFAULT_TAG_MAP maps `review` (on Meridian.A.2) and
        # `review-v2` (on Meridian.C.5) both to `review` — legal,
        # the version dirs differ.
        project = build_letter_family_threads(tmp_path)
        tag_map = write_tag_map(tmp_path / "tag-map.json", DEFAULT_TAG_MAP)
        plan = build_adopt_family_plan(
            project, tag_map_path=tag_map, artifact_type=ARTIFACT_TYPE
        )
        targets = sorted(
            new for _, _, new in plan.tag_resolution if new.endswith("review")
        )
        assert targets == ["meridian-a.2.review", "meridian-c.5.review"]


class TestResolution:
    def test_review_v2_remap_resolves_to_canonical_review(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        tag_map = write_tag_map(tmp_path / "tag-map.json", DEFAULT_TAG_MAP)
        plan = build_adopt_family_plan(
            project, tag_map_path=tag_map, artifact_type=ARTIFACT_TYPE
        )
        resolution = {old: new for _, old, new in plan.tag_resolution}
        assert resolution["Meridian.C.5.review-v2"] == "meridian-c.5.review"

    def test_identity_mappings_resolve_in_place(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        tag_map = write_tag_map(tmp_path / "tag-map.json", DEFAULT_TAG_MAP)
        plan = build_adopt_family_plan(
            project, tag_map_path=tag_map, artifact_type=ARTIFACT_TYPE
        )
        resolution = {old: new for _, old, new in plan.tag_resolution}
        assert resolution["Meridian.C.7.s101"] == "meridian-c.7.s101"
        assert resolution["Meridian.C.7.audit2"] == "meridian-c.7.audit2"
        assert (
            resolution["Meridian.C.5.pre_flight"]
            == "meridian-c.5.pre_flight"
        )
