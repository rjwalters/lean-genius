"""Plan-construction tests for `--adopt-family` (issue #440).

Covers: multi-family DocumentPlans with derived slugs (NO --slug in
this mode), the REQUIRED invocation-wide `--artifact-type` (missing →
refusal naming the two likely ip candidates; two-tier #394 validation;
both ip types registered as skill-identity values), slug collision
refusals (BRIEF entry / on-disk dir / cross-family after sanitization /
target version dir), BRIEF-mode selection, the BRIEF-less-root
refusal, and the dry-run report surface (resolution table + full BRIEF
preview).
"""

from __future__ import annotations

import pytest

from _fixtures import (
    DEFAULT_TAG_MAP,
    ENROLL_OPERATOR_BRIEF,
    build_letter_family_threads,
    write_tag_map,
)
from _project_migrate_skill_lib import adopt_family, detect, orchestrate

build_adopt_family_plan = adopt_family.build_adopt_family_plan
AdoptFamilyError = adopt_family.AdoptFamilyError
run_adopt_family = orchestrate.run_adopt_family
Shape = detect.Shape

ARTIFACT_TYPE = "ip-uspto-provisional"


def _tag_map(tmp_path, mapping=None):
    return write_tag_map(
        tmp_path / "tag-map.json", mapping or DEFAULT_TAG_MAP
    )


class TestMultiFamilyPlans:
    def test_each_family_gets_its_own_document_plan(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = build_adopt_family_plan(
            project,
            tag_map_path=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        assert [d.slug for d in plan.documents] == [
            "meridian-a",
            "meridian-c",
        ]
        for doc in plan.documents:
            assert doc.brief_merge is not None
            assert doc.brief_merge.slug == doc.slug
            assert doc.target_dir == project / doc.slug

    def test_renames_relocate_under_derived_slug_dirs(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = build_adopt_family_plan(
            project,
            tag_map_path=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        rename_map = {
            r.source.name: r.target
            for d in plan.documents
            for r in d.renames
        }
        assert (
            rename_map["Meridian.C.7"]
            == project / "meridian-c" / "meridian-c.7"
        )
        assert (
            rename_map["Meridian.C.7.enablement"]
            == project / "meridian-c" / "meridian-c.7.enablement"
        )

    def test_project_root_is_the_family_dir_itself(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = build_adopt_family_plan(
            project,
            tag_map_path=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        assert plan.project_dir == project

    def test_no_slug_parameter_exists(self):
        # Slugs are derived, not flagged (issue #440 curation): the
        # planner deliberately exposes no slug override.
        import inspect

        params = inspect.signature(build_adopt_family_plan).parameters
        assert "slug" not in params
        run_params = inspect.signature(run_adopt_family).parameters
        assert "slug" not in run_params


class TestArtifactTypeRequired:
    def test_missing_artifact_type_refused_naming_ip_candidates(
        self, tmp_path
    ):
        project = build_letter_family_threads(tmp_path)
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project, tag_map_path=_tag_map(tmp_path)
            )
        msg = str(excinfo.value)
        assert "--artifact-type" in msg
        assert "ip-uspto" in msg
        assert "ip-uspto-provisional" in msg

    @pytest.mark.parametrize(
        "value", ["ip-uspto", "ip-uspto-provisional"]
    )
    def test_both_ip_types_validate_two_tier(self, tmp_path, value):
        pytest.importorskip("anvil.lib.project_brief")
        project = build_letter_family_threads(tmp_path)
        plan = build_adopt_family_plan(
            project,
            tag_map_path=_tag_map(tmp_path),
            artifact_type=value,
        )
        for doc in plan.documents:
            assert doc.brief_merge.artifact_type == value

    def test_unregistered_type_refused_two_tier(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        project = build_letter_family_threads(tmp_path)
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=_tag_map(tmp_path),
                artifact_type="patent-thing",
            )
        assert "patent-thing" in str(excinfo.value)

    def test_invocation_wide_todo_marker_on_every_entry(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = build_adopt_family_plan(
            project,
            tag_map_path=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        for doc in plan.documents:
            bm = doc.brief_merge
            assert bm.todo_comment is not None
            assert "invocation-wide" in bm.todo_comment
            assert "TODO(operator)" in bm.todo_comment
            # Operator-supplied, not inferred — but still confirmed.
            assert not bm.inferred
            assert doc.operator_todos

    def test_ip_types_are_registered_skill_identity_values(self):
        # The #440 registry addition (the #432 `report` precedent):
        # the required values must survive strict BRIEF validation.
        pytest.importorskip("anvil.lib.project_brief")
        from anvil.lib.project_brief import (
            MEMO_ARTIFACT_TYPES,
            REGISTERED_ARTIFACT_TYPES,
            SKILL_IDENTITY_ARTIFACT_TYPES,
        )

        for value in ("ip-uspto", "ip-uspto-provisional"):
            assert value in REGISTERED_ARTIFACT_TYPES
            assert value in SKILL_IDENTITY_ARTIFACT_TYPES
            assert value not in MEMO_ARTIFACT_TYPES


class TestBriefMode:
    def test_no_enclosing_brief_synthesizes(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        plan = build_adopt_family_plan(
            project,
            tag_map_path=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        assert plan.brief_mode == "render"
        assert plan.synthesize_brief

    def test_existing_brief_appends(self, tmp_path):
        project = build_letter_family_threads(
            tmp_path, with_project_brief=True
        )
        plan = build_adopt_family_plan(
            project,
            tag_map_path=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        assert plan.brief_mode == "append"
        assert not plan.synthesize_brief
        assert plan.preexisting_brief_slugs == ["zeta-memo", "alpha-memo"]


class TestCollisions:
    def test_slug_already_in_brief_refused(self, tmp_path):
        # An existing BRIEF already lists the derived slug
        # `meridian-c` (listed-but-missing is only a warning at strict
        # parse time, so the BRIEF itself validates).
        project = build_letter_family_threads(tmp_path)
        (project / "BRIEF.md").write_text(
            "---\n"
            "project: agent-workspace\n"
            "documents:\n"
            "  - slug: meridian-c\n"
            "    artifact_type: investment-memo\n"
            "---\n\nBody.\n",
            encoding="utf-8",
        )
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=_tag_map(tmp_path),
                artifact_type=ARTIFACT_TYPE,
            )
        msg = str(excinfo.value)
        assert "Slug collision" in msg
        assert "meridian-c" in msg
        assert "Meridian.C" in msg

    def test_target_dir_occupied_refused(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        (project / "meridian-c").mkdir()
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=_tag_map(tmp_path),
                artifact_type=ARTIFACT_TYPE,
            )
        msg = str(excinfo.value)
        assert "meridian-c" in msg
        assert "Nothing was modified" in msg

    def test_cross_family_sanitized_slug_collision_refused(
        self, tmp_path
    ):
        # Two stems differing only in case sanitize to the same slug.
        project = build_letter_family_threads(tmp_path)
        (project / "meridian.c.1").mkdir()
        (project / "meridian.c.1" / "spec.md").write_text(
            "# b\n", encoding="utf-8"
        )
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=_tag_map(tmp_path),
                artifact_type=ARTIFACT_TYPE,
            )
        msg = str(excinfo.value)
        assert "Cross-family slug collision" in msg
        assert "`Meridian.C`" in msg and "`meridian.c`" in msg
        assert "`meridian-c`" in msg

    def test_unparseable_existing_brief_refused(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        (project / "BRIEF.md").write_text(
            "no frontmatter at all\n", encoding="utf-8"
        )
        with pytest.raises(AdoptFamilyError):
            build_adopt_family_plan(
                project,
                tag_map_path=_tag_map(tmp_path),
                artifact_type=ARTIFACT_TYPE,
            )

    def test_briefless_root_with_other_threads_refused(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        other = project / "other-thread" / "other-thread.1"
        other.mkdir(parents=True)
        (other / "other-thread.md").write_text("# o\n", encoding="utf-8")
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=_tag_map(tmp_path),
                artifact_type=ARTIFACT_TYPE,
            )
        assert "other-thread" in str(excinfo.value)
        assert "project-migrate" in str(excinfo.value)

    def test_pre_existing_target_tree_refused_pre_mutation(self, tmp_path):
        # Unlike --adopt-vn (whose default rename is in-place), every
        # adopt-family target lives under a NEW `<slug>/` dir — so a
        # pre-existing target tree always trips the slug-dir collision,
        # before any version-dir target could clobber.
        project = build_letter_family_threads(tmp_path)
        (project / "meridian-a" / "meridian-a.1").mkdir(parents=True)
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=_tag_map(tmp_path),
                artifact_type=ARTIFACT_TYPE,
            )
        msg = str(excinfo.value)
        assert "meridian-a" in msg
        assert "Nothing was modified" in msg


class TestReport:
    def test_dry_run_report_includes_renames_resolution_and_preview(
        self, tmp_path
    ):
        project = build_letter_family_threads(tmp_path)
        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        assert result.success
        assert result.shape is Shape.ADOPT_FAMILY
        report = result.report
        assert (
            "Rename: `Meridian.C.7` → `meridian-c/meridian-c.7`" in report
        )
        assert "## Sidecar tag resolution" in report
        assert (
            "`Meridian.C.5.review-v2/` → `meridian-c.5.review/`" in report
        )
        assert "## Proposed `BRIEF.md`" in report
        assert "slug: meridian-a" in report
        assert "slug: meridian-c" in report
        assert "# TODO(operator)" in report
        assert "## Strays (left untouched)" in report
        assert "notes-archive" in report

    def test_append_mode_preview_preserves_operator_prefix(self, tmp_path):
        project = build_letter_family_threads(
            tmp_path, with_project_brief=True
        )
        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        original_fm_end = ENROLL_OPERATOR_BRIEF.index("\n---\n", 4)
        assert ENROLL_OPERATOR_BRIEF[:original_fm_end] in result.report
        assert (
            "slug: meridian-a  # adopted-from: Meridian.A.{N}"
            in result.report
        )


class TestLeadingZeroAmbiguity:
    """Leading-zero slot collapse refusals (issue #458).

    `Meridian.C.07/` + `Meridian.C.7/` both parse to `Meridian.C`
    version slot 7: the dict-keyed scan silently dropped one. Duplicate
    sidecar slots previously fell through to the misleading
    `seen_targets` "already exists" message. Both are now scan-time
    refusals naming the stem and every colliding dir; the whole batch
    (clean sibling families included) aborts.
    """

    def test_duplicate_version_slot_refused_naming_both_and_stem(
        self, tmp_path
    ):
        project = build_letter_family_threads(
            tmp_path, with_sidecars=False, with_leading_zero_dup=True
        )
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(project, artifact_type=ARTIFACT_TYPE)
        msg = str(excinfo.value)
        assert "`Meridian.C.07/`" in msg
        assert "`Meridian.C.7/`" in msg
        assert "`Meridian.C` version 7" in msg
        assert "Nothing was modified" in msg

    def test_refusal_fires_at_scan_time_before_required_flags(
        self, tmp_path
    ):
        # Missing --artifact-type (and missing --tag-map with sidecars
        # present) are refusals too — the scan-time ambiguity refusal
        # must win over both.
        project = build_letter_family_threads(
            tmp_path, with_leading_zero_dup=True
        )
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(project)
        assert "Ambiguous version numbering" in str(excinfo.value)

    def test_whole_batch_aborts_with_clean_sibling_family(self, tmp_path):
        # Meridian.A is collision-free, but the batch contract aborts
        # EVERYTHING pre-mutation: the raise means no plan exists for
        # the clean family either.
        project = build_letter_family_threads(
            tmp_path, with_sidecars=False, with_leading_zero_dup=True
        )
        with pytest.raises(AdoptFamilyError):
            build_adopt_family_plan(project, artifact_type=ARTIFACT_TYPE)
        assert not (project / "meridian-a").exists()
        assert not (project / "BRIEF.md").exists()

    def test_duplicate_sidecar_slot_refused_at_plan_time(self, tmp_path):
        # Single version dir (Meridian.C.7/) with a leading-zero twin
        # of one of its sidecars: previously this fell through to the
        # misleading seen_targets "already exists" refusal — now it is
        # a scan-time ambiguity refusal naming both sidecar dirs.
        project = build_letter_family_threads(tmp_path)
        dup = project / "Meridian.C.07.enablement"
        dup.mkdir()
        (dup / "review.md").write_text("# dup\n", encoding="utf-8")
        with pytest.raises(AdoptFamilyError) as excinfo:
            build_adopt_family_plan(
                project,
                tag_map_path=_tag_map(tmp_path),
                artifact_type=ARTIFACT_TYPE,
            )
        msg = str(excinfo.value)
        assert "`Meridian.C.07.enablement/`" in msg
        assert "`Meridian.C.7.enablement/`" in msg
        assert "`enablement` sidecar" in msg
        assert "Nothing was modified" in msg
        assert "already exists" not in msg

    def test_lone_leading_zero_dir_adopts_normalized(self, tmp_path):
        # No Meridian.C.7 sibling for slot 17: a lone Meridian.C.017
        # is NOT a refusal — it adopts, normalized to meridian-c.17.
        project = build_letter_family_threads(tmp_path, with_sidecars=False)
        lone = project / "Meridian.C.017"
        lone.mkdir()
        (lone / "spec.md").write_text("# v017\n", encoding="utf-8")
        plan = build_adopt_family_plan(project, artifact_type=ARTIFACT_TYPE)
        renames = {
            r.source.name: r.target
            for doc in plan.documents
            for r in doc.renames
        }
        assert (
            renames["Meridian.C.017"]
            == project / "meridian-c" / "meridian-c.17"
        )
