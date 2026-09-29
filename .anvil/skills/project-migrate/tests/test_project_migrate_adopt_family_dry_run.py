"""Dry-run contract tests for `--adopt-family` (issue #440).

Dry-run is the universal default (``apply=False``): the run must leave
the tree byte-identical (digest check) while the report carries the
full per-directory sidecar tag resolution AND the full proposed BRIEF —
rendered through the SAME ``render_enroll_brief`` code path the apply
step writes, so the preview equals the eventual write byte-for-byte
(both the synthesis and the surgical-append variants).
"""

from __future__ import annotations


import pytest

from _fixtures import (
    DEFAULT_TAG_MAP,
    build_letter_family_threads,
    write_tag_map,
)
from _project_migrate_skill_lib import adopt_family, orchestrate
from anvil.lib.testing import tree_hash as _tree_digest

run_adopt_family = orchestrate.run_adopt_family
AdoptFamilyError = adopt_family.AdoptFamilyError

ARTIFACT_TYPE = "ip-uspto-provisional"


def _tag_map(tmp_path):
    return write_tag_map(tmp_path / "tag-map.json", DEFAULT_TAG_MAP)


def _previewed_brief(report: str) -> str:
    fence_start = report.index("````markdown\n") + len("````markdown\n")
    fence_end = report.index("\n````", fence_start)
    return report[fence_start:fence_end]


class TestAdoptFamilyDryRun:
    def test_dry_run_is_default_and_mutates_nothing(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        before = _tree_digest(project)

        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )

        assert result.success
        assert result.apply_result is None
        assert _tree_digest(project) == before

    def test_dry_run_with_existing_brief_mutates_nothing(self, tmp_path):
        project = build_letter_family_threads(
            tmp_path, with_project_brief=True
        )
        before = _tree_digest(project)
        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        assert result.success
        assert _tree_digest(project) == before

    def test_noop_run_mutates_nothing_even_under_apply(self, tmp_path):
        empty = tmp_path / "proj"
        empty.mkdir(parents=True)
        before = _tree_digest(tmp_path)
        result = run_adopt_family(empty, apply=True)
        assert result.success
        assert result.apply_result is None
        assert "nothing to adopt" in result.report
        assert _tree_digest(tmp_path) == before

    def test_dry_run_prints_full_tag_resolution(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        result = run_adopt_family(
            project,
            tag_map=_tag_map(tmp_path),
            artifact_type=ARTIFACT_TYPE,
        )
        report = result.report
        assert "## Sidecar tag resolution" in report
        # EVERY renameable sidecar's old name → new name appears.
        for old, new in (
            ("Meridian.A.2.review", "meridian-a.2.review"),
            ("Meridian.C.5.review-v2", "meridian-c.5.review"),
            ("Meridian.C.5.pre_flight", "meridian-c.5.pre_flight"),
            ("Meridian.C.7.enablement", "meridian-c.7.enablement"),
            ("Meridian.C.7.s101", "meridian-c.7.s101"),
            ("Meridian.C.7.audit", "meridian-c.7.audit"),
            ("Meridian.C.7.audit2", "meridian-c.7.audit2"),
        ):
            assert f"`{old}/` → `{new}/`" in report

    def test_preview_matches_apply_write_synthesis(self, tmp_path):
        project = build_letter_family_threads(tmp_path)
        tag_map = _tag_map(tmp_path)

        preview = run_adopt_family(
            project, tag_map=tag_map, artifact_type=ARTIFACT_TYPE
        )
        previewed = _previewed_brief(preview.report)

        applied = run_adopt_family(
            project,
            tag_map=tag_map,
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert applied.success, applied.report
        written = (project / "BRIEF.md").read_text(encoding="utf-8")
        assert written.rstrip("\n") == previewed.rstrip("\n")

    def test_preview_matches_apply_write_append(self, tmp_path):
        project = build_letter_family_threads(
            tmp_path, with_project_brief=True
        )
        tag_map = _tag_map(tmp_path)

        preview = run_adopt_family(
            project, tag_map=tag_map, artifact_type=ARTIFACT_TYPE
        )
        previewed = _previewed_brief(preview.report)

        applied = run_adopt_family(
            project,
            tag_map=tag_map,
            artifact_type=ARTIFACT_TYPE,
            apply=True,
        )
        assert applied.success, applied.report
        written = (project / "BRIEF.md").read_text(encoding="utf-8")
        assert written.rstrip("\n") == previewed.rstrip("\n")

    def test_leading_zero_refusal_mutates_nothing_even_under_apply(
        self, tmp_path
    ):
        # Issue #458: the Meridian.C.07/Meridian.C.7 slot collision
        # refuses at scan time — the whole batch (the clean Meridian.A
        # family included) stays byte-identical even with apply=True.
        project = build_letter_family_threads(
            tmp_path, with_leading_zero_dup=True
        )
        before = _tree_digest(project)
        with pytest.raises(AdoptFamilyError):
            run_adopt_family(
                project,
                tag_map=_tag_map(tmp_path),
                artifact_type=ARTIFACT_TYPE,
                apply=True,
            )
        assert _tree_digest(project) == before

    def test_duplicate_sidecar_slot_refusal_mutates_nothing_under_apply(
        self, tmp_path
    ):
        # Issue #458: a leading-zero sidecar twin on a single version
        # dir is a plan-time refusal (not the old misleading
        # seen_targets message) — tree untouched under apply=True.
        project = build_letter_family_threads(tmp_path)
        dup = project / "Meridian.C.07.enablement"
        dup.mkdir()
        (dup / "review.md").write_text("# dup\n", encoding="utf-8")
        before = _tree_digest(project)
        with pytest.raises(AdoptFamilyError):
            run_adopt_family(
                project,
                tag_map=_tag_map(tmp_path),
                artifact_type=ARTIFACT_TYPE,
                apply=True,
            )
        assert _tree_digest(project) == before
