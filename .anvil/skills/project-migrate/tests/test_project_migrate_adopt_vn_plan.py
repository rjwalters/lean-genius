"""Plan-construction tests for `--adopt-vn` (issue #432 Phase 1).

Covers: rename mapping (in-place default + `--slug` relocation), slug
default sanitization + canonical-only `--slug` validation, artifact-type
inference (`report` + TODO marker) and the two-tier `--artifact-type`
validation, collision refusals (BRIEF entry / target dir / target
version dir), BRIEF-mode selection, the dry-run report's full BRIEF
preview, and the leading-zero slot-collapse refusals (issue #458).
"""

from __future__ import annotations

import pytest

from _fixtures import ENROLL_OPERATOR_BRIEF, build_vn_report_dirs
from _project_migrate_skill_lib import adopt_vn, detect, orchestrate

build_adopt_vn_plan = adopt_vn.build_adopt_vn_plan
AdoptVnError = adopt_vn.AdoptVnError
run_adopt_vn = orchestrate.run_adopt_vn
Shape = detect.Shape


class TestRenames:
    def test_default_slug_renames_in_place(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        plan = build_adopt_vn_plan(reports)
        doc = plan.documents[0]
        assert doc.slug == "reports"
        assert doc.target_dir == reports  # in-place
        rename_map = {r.source.name: r.target for r in doc.renames}
        assert rename_map["v3"] == reports / "reports.3"
        assert rename_map["v3.review"] == reports / "reports.3.review"
        # Renames are version-ascending with sidecars riding alongside.
        names = [r.source.name for r in doc.renames]
        assert names == ["v1", "v2", "v3", "v3.review", "v5", "v5.review"]

    def test_slug_override_relocates_to_project_root(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        project = reports.parent
        plan = build_adopt_vn_plan(reports, slug="quarterly")
        doc = plan.documents[0]
        assert doc.target_dir == project / "quarterly"
        rename_map = {r.source.name: r.target for r in doc.renames}
        assert rename_map["v3"] == project / "quarterly" / "quarterly.3"
        assert (
            rename_map["v3.review"]
            == project / "quarterly" / "quarterly.3.review"
        )

    def test_project_root_is_family_dir_parent(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        plan = build_adopt_vn_plan(reports)
        assert plan.project_dir == reports.parent


class TestSlug:
    def test_default_slug_sanitizes_dir_name(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, dir_name="Q3_Reports")
        plan = build_adopt_vn_plan(reports)
        assert plan.documents[0].slug == "q3-reports"

    def test_non_canonical_explicit_slug_refused(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports, slug="Not_Canonical")
        assert "not canonical" in str(excinfo.value)

    def test_unsanitizable_dir_name_demands_slug(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, dir_name="###")
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports)
        assert "--slug" in str(excinfo.value)


class TestArtifactType:
    def test_inferred_report_with_todo_marker(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        plan = build_adopt_vn_plan(reports)
        bm = plan.documents[0].brief_merge
        assert bm is not None
        assert bm.artifact_type == "report"
        assert bm.inferred
        assert bm.todo_comment is not None
        assert "TODO(operator)" in bm.todo_comment
        assert plan.documents[0].operator_todos

    def test_explicit_registered_type_no_todo(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        plan = build_adopt_vn_plan(reports, artifact_type="position-paper")
        bm = plan.documents[0].brief_merge
        assert bm.artifact_type == "position-paper"
        assert not bm.inferred
        assert bm.todo_comment is None

    def test_unregistered_type_refused_two_tier(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        reports = build_vn_report_dirs(tmp_path)
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports, artifact_type="quarterly-report")
        assert "quarterly-report" in str(excinfo.value)

    def test_report_is_registered_skill_identity_type(self):
        # The #432 registry addition (the #408 `pub`/`paper` precedent): the
        # inferred default must survive strict BRIEF validation.
        pytest.importorskip("anvil.lib.project_brief")
        from anvil.lib.project_brief import (
            MEMO_ARTIFACT_TYPES,
            REGISTERED_ARTIFACT_TYPES,
            SKILL_IDENTITY_ARTIFACT_TYPES,
        )

        assert "report" in REGISTERED_ARTIFACT_TYPES
        assert "report" in SKILL_IDENTITY_ARTIFACT_TYPES
        assert "report" not in MEMO_ARTIFACT_TYPES


class TestBriefMode:
    def test_no_enclosing_brief_synthesizes(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        plan = build_adopt_vn_plan(reports)
        assert plan.brief_mode == "render"
        assert plan.synthesize_brief

    def test_enclosing_brief_appends(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_project_brief=True)
        plan = build_adopt_vn_plan(reports)
        assert plan.brief_mode == "append"
        assert not plan.synthesize_brief
        assert plan.preexisting_brief_slugs == ["zeta-memo", "alpha-memo"]


class TestCollisions:
    def test_slug_already_in_brief_refused(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_project_brief=True)
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports, slug="zeta-memo")
        assert "zeta-memo" in str(excinfo.value)
        assert "--slug" in str(excinfo.value)

    def test_target_dir_occupied_refused(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_project_brief=True)
        with pytest.raises(AdoptVnError) as excinfo:
            # alpha-memo exists on disk but use a name colliding with a
            # plain occupied path instead of a BRIEF slug.
            build_adopt_vn_plan(reports, slug="alpha-memo")
        assert "alpha-memo" in str(excinfo.value)

    def test_target_version_dir_collision_refused(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        (reports / "reports.3").mkdir()
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports)
        msg = str(excinfo.value)
        assert "reports.3" in msg
        assert "Nothing was modified" in msg

    def test_unparseable_existing_brief_refused(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        (reports.parent / "BRIEF.md").write_text(
            "---\nproject: p\ndocuments:\n  - slug: x\n---\n",
            encoding="utf-8",
        )
        # The BRIEF parses minimally but strict validate_dirs would
        # warn about x being unstarted — that is fine. Now break it:
        (reports.parent / "BRIEF.md").write_text(
            "no frontmatter at all\n", encoding="utf-8"
        )
        with pytest.raises(AdoptVnError):
            build_adopt_vn_plan(reports)

    def test_briefless_root_with_other_threads_refused(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        other = reports.parent / "other-thread" / "other-thread.1"
        other.mkdir(parents=True)
        (other / "other-thread.md").write_text("# o\n", encoding="utf-8")
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports)
        assert "other-thread" in str(excinfo.value)
        assert "project-migrate" in str(excinfo.value)


class TestReport:
    def test_dry_run_report_includes_renames_and_brief_preview(
        self, tmp_path
    ):
        reports = build_vn_report_dirs(tmp_path)
        result = run_adopt_vn(reports)
        assert result.success
        assert result.shape is Shape.ADOPT_VN
        assert "Rename: `reports/v3` → `reports/reports.3`" in result.report
        assert (
            "Rename: `reports/v3.review` → `reports/reports.3.review`"
            in result.report
        )
        assert "## Proposed `BRIEF.md`" in result.report
        assert "slug: reports" in result.report
        assert "# TODO(operator)" in result.report

    def test_append_mode_preview_preserves_operator_prefix(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_project_brief=True)
        result = run_adopt_vn(reports)
        original_fm_end = ENROLL_OPERATOR_BRIEF.index("\n---\n", 4)
        assert ENROLL_OPERATOR_BRIEF[:original_fm_end] in result.report
        assert "slug: reports  # adopted-from: reports/vN" in result.report


class TestLeadingZeroAmbiguity:
    """Leading-zero slot collapse refusals (issue #458).

    `v07/` + `v7/` both parse to version slot 7: the dict-keyed scan
    silently dropped one, and same-slot sidecars (`v07.review/` +
    `v7.review/`) planned two renames to ONE target with no in-plan
    guard — failing mid-apply. Both are now scan-time refusals naming
    every colliding dir; a LONE `v07` still adopts, normalized.
    """

    def test_duplicate_version_slot_refused_naming_both(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_leading_zero_dup=True)
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports)
        msg = str(excinfo.value)
        assert "`v07/`" in msg
        assert "`v7/`" in msg
        assert "version 7" in msg
        assert "Nothing was modified" in msg

    def test_refusal_fires_at_scan_time_before_slug_work(self, tmp_path):
        # A non-canonical --slug would refuse too — the ambiguity
        # refusal must win (scan time precedes all slug/BRIEF work).
        reports = build_vn_report_dirs(tmp_path, with_leading_zero_dup=True)
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports, slug="Not_Canonical")
        assert "Ambiguous version numbering" in str(excinfo.value)

    def test_duplicate_sidecar_slot_refused_at_plan_time(self, tmp_path):
        # Single version dir (v3/) with BOTH v03.review/ and v3.review/:
        # previously both renames targeted <slug>.3.review and the
        # collision only surfaced MID-APPLY. Now: plan-time refusal.
        reports = build_vn_report_dirs(tmp_path)
        dup = reports / "v03.review"
        dup.mkdir()
        (dup / "review.md").write_text("# dup\n", encoding="utf-8")
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports)
        msg = str(excinfo.value)
        assert "`v03.review/`" in msg
        assert "`v3.review/`" in msg
        assert "`review` sidecar" in msg
        assert "Nothing was modified" in msg

    def test_three_way_collision_names_every_dir(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path, with_leading_zero_dup=True)
        third = reports / "v007"
        third.mkdir()
        (third / "report.md").write_text("# v007\n", encoding="utf-8")
        with pytest.raises(AdoptVnError) as excinfo:
            build_adopt_vn_plan(reports)
        msg = str(excinfo.value)
        assert "`v007/`" in msg
        assert "`v07/`" in msg
        assert "`v7/`" in msg
        assert "all parse to version 7" in msg

    def test_lone_leading_zero_dir_adopts_normalized(self, tmp_path):
        # No v7 sibling: a lone v07 is NOT a refusal — it adopts,
        # normalized to <slug>.7.
        reports = build_vn_report_dirs(tmp_path)
        lone = reports / "v07"
        lone.mkdir()
        (lone / "report.md").write_text("# v07\n", encoding="utf-8")
        plan = build_adopt_vn_plan(reports)
        rename_map = {
            r.source.name: r.target for r in plan.documents[0].renames
        }
        assert rename_map["v07"] == reports / "reports.7"

    def test_lone_leading_zero_dir_applies_normalized(self, tmp_path):
        reports = build_vn_report_dirs(tmp_path)
        lone = reports / "v07"
        lone.mkdir()
        (lone / "report.md").write_text("# v07\n", encoding="utf-8")
        result = run_adopt_vn(reports, apply=True)
        assert result.success, result.report
        assert (reports / "reports.7" / "report.md").is_file()
        assert not (reports / "v07").exists()
