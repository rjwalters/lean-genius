"""Rescore tests for `--adopt-review --rescore` (issue #507 — Phase 3b).

The operator-driven LLM rescore turns a Phase-3a unscored stub into a real
scored `_review.json`. The Python is a thin planner + marker-flip +
atomic-write harness (the LLM scoring step stays in the slash-command
runtime). These tests cover:

- planner: finds only `unscored:true` + `source:foreign-adopted` stubs;
  ignores real reviews and already-rescored sidecars; idempotent no-op on
  a fully-rescored tree.
- dry-run safety: `--rescore` without `--apply` leaves the tree
  byte-identical.
- scored write: after apply, `_review.json` validates against
  `review_schema` with `unscored:false`, populated scores/total/verdict,
  and the rubric-stamping fields; `_meta.json` carries
  `rescored_from: foreign-adopted` + `origin_filename`.
- verbatim preservation + atomicity: `review.md` byte-identical; an
  injected mid-write failure restores the original stub.
- honesty guard: a stub whose rubric cannot be resolved is SKIPPED with a
  note, never guessed.
"""

from __future__ import annotations

import hashlib
import json

import pytest

from anvil.lib.testing import tree_hash as _tree_digest
from _fixtures import FOREIGN_REVIEW_PROSE, build_adopted_review_threads
from _project_migrate_skill_lib import adopt_review, orchestrate

run_adopt_review = orchestrate.run_adopt_review

# The fixture's two threads, scored as ip-uspto (/45, advance 39). The
# scores enumerate two dims; total derives from them.
_IP_BRIEF = (
    "---\n"
    "documents:\n"
    "  - slug: meridian-c\n"
    "    artifact_type: ip-uspto\n"
    "  - slug: meridian-a\n"
    "    artifact_type: ip-uspto\n"
    "---\n"
    "# Project BRIEF\n"
)


def _digest(path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _build_rescorable_tree(tmp_path, *, with_brief: bool = True):
    """A POST-Phase-3a tree: every foreign sidecar carries an unscored stub.

    With ``with_brief`` a project BRIEF declares both threads as
    ``ip-uspto`` so the rubric resolves (BRIEF route). Without it, no
    BRIEF + ``spec.md`` bodies → rubric is unresolvable (honesty-guard
    fixture).
    """
    project = build_adopted_review_threads(tmp_path, pre_converted=True)
    if with_brief:
        (project / "BRIEF.md").write_text(_IP_BRIEF, encoding="utf-8")
    return project


def _score(dimension, value, maximum=10, critical=False):
    return adopt_review.Score(
        dimension=dimension, score=value, max=maximum, critical=critical
    )


def _scored_map(plan, *, value=8):
    """Build a {sidecar_name: ScoredReviewInput} for every plan target."""
    out = {}
    for target in plan.targets:
        out[target.sidecar_dir.name] = adopt_review.ScoredReviewInput(
            sidecar_name=target.sidecar_dir.name,
            scores=[
                _score("disclosure", value),
                _score("claim_scope", value),
            ],
        )
    return out


class TestPlanner:
    def test_finds_only_foreign_stubs(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        plan = adopt_review.build_rescore_plan(project)
        names = sorted(t.sidecar_dir.name for t in plan.targets)
        assert names == [
            "meridian-a.2.review",
            "meridian-c.5.review",
            "meridian-c.7.enablement",
            "meridian-c.7.s101",
        ]
        # Each target resolved the ip-uspto rubric (via BRIEF).
        for target in plan.targets:
            assert target.skill == "ip-uspto"
            assert target.skill_source == "brief"
            assert target.rubric.id == "anvil-ip-uspto-v2"
            assert target.rubric.total == 45
            assert target.rubric.advance_threshold == 39

    def test_ignores_real_review_sibling(self, tmp_path):
        # A genuinely-scored co-sibling must NOT be planned for rescore.
        project = build_adopted_review_threads(
            tmp_path, pre_converted=True, with_real_sibling=True
        )
        (project / "BRIEF.md").write_text(_IP_BRIEF, encoding="utf-8")
        plan = adopt_review.build_rescore_plan(project)
        names = {t.sidecar_dir.name for t in plan.targets}
        assert "meridian-c.7.audit" not in names
        skipped = {n for n, _ in plan.skipped}
        assert "meridian-c.7.audit" in skipped

    def test_idempotent_noop_on_rescored_tree(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        plan = adopt_review.build_rescore_plan(project)
        scored = _scored_map(plan)
        result = run_adopt_review(
            project, rescore=True, apply=True, scored_reviews=scored
        )
        assert result.success, result.report

        # Re-plan: no unscored stub remains.
        plan2 = adopt_review.build_rescore_plan(project)
        assert plan2.is_noop
        assert plan2.targets == []

    def test_empty_plan_when_no_stub_present(self, tmp_path):
        # A tree with NO Phase-3a stub (raw review.md-only sidecars) yields
        # an empty plan, not an error.
        project = build_adopted_review_threads(tmp_path)  # not pre_converted
        (project / "BRIEF.md").write_text(_IP_BRIEF, encoding="utf-8")
        plan = adopt_review.build_rescore_plan(project)
        assert plan.is_noop
        assert plan.targets == []

    def test_missing_directory_raises(self, tmp_path):
        with pytest.raises(adopt_review.AdoptReviewError):
            adopt_review.build_rescore_plan(tmp_path / "does-not-exist")


class TestDryRunSafety:
    def test_dry_run_zero_mutation(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        before = _tree_digest(project)
        result = run_adopt_review(project, rescore=True)  # no apply
        assert result.success
        assert result.apply_result is None
        assert _tree_digest(project) == before

    def test_dry_run_report_lists_targets_and_rubric(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        result = run_adopt_review(project, rescore=True)
        report = result.report
        assert "Phase 3b" in report
        assert "meridian-c.7.enablement" in report
        assert "anvil-ip-uspto-v2" in report
        assert "ip-uspto" in report

    def test_apply_without_scores_leaves_honest_stubs(self, tmp_path):
        # --rescore --apply but no operator scores supplied: nothing is
        # fabricated; every target stays an honest stub.
        project = _build_rescorable_tree(tmp_path)
        before = _tree_digest(project)
        result = run_adopt_review(
            project, rescore=True, apply=True, scored_reviews={}
        )
        assert result.success
        assert result.apply_result.rescored == []
        assert len(result.apply_result.skipped_no_input) == 4
        assert _tree_digest(project) == before


class TestScoredWrite:
    def test_scored_review_validates_and_flips_unscored(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        plan = adopt_review.build_rescore_plan(project)
        scored = _scored_map(plan, value=8)
        result = run_adopt_review(
            project, rescore=True, apply=True, scored_reviews=scored
        )
        assert result.success, result.report
        assert sorted(result.apply_result.rescored) == [
            "meridian-a.2.review",
            "meridian-c.5.review",
            "meridian-c.7.enablement",
            "meridian-c.7.s101",
        ]

        sidecar = project / "meridian-c" / "meridian-c.7.enablement"
        review_raw = json.loads((sidecar / "_review.json").read_text())
        # Validates against the schema (unscored=False requires scores).
        review = adopt_review.Review.model_validate(review_raw)
        assert review.unscored is False
        assert len(review.scores) == 2
        assert review.total == 16  # 8 + 8
        assert review.threshold == 39
        assert review.verdict == adopt_review.Verdict.REVISE  # 16 < 39
        assert review.rubric == "anvil-ip-uspto-v2"

        marker = json.loads((sidecar / "_meta.json").read_text())
        assert marker["unscored"] is False
        assert marker["rescored_from"] == "foreign-adopted"
        assert marker["source"] == "foreign-adopted"
        assert marker["origin_filename"] == "review.md"
        assert marker["rubric_id"] == "anvil-ip-uspto-v2"
        assert marker["rubric_total"] == 45
        assert marker["advance_threshold"] == 39

    def test_advance_verdict_when_total_meets_threshold(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        plan = adopt_review.build_rescore_plan(project)
        # Two dims at 20 each (max 25) → total 40 >= 39 → ADVANCE.
        scored = {}
        for target in plan.targets:
            scored[target.sidecar_dir.name] = adopt_review.ScoredReviewInput(
                sidecar_name=target.sidecar_dir.name,
                scores=[
                    _score("a", 20, maximum=25),
                    _score("b", 20, maximum=25),
                ],
            )
        result = run_adopt_review(
            project, rescore=True, apply=True, scored_reviews=scored
        )
        assert result.success, result.report
        sidecar = project / "meridian-a" / "meridian-a.2.review"
        review = adopt_review.Review.model_validate(
            json.loads((sidecar / "_review.json").read_text())
        )
        assert review.total == 40
        assert review.verdict == adopt_review.Verdict.ADVANCE

    def test_critical_flag_forces_block(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        plan = adopt_review.build_rescore_plan(project)
        scored = {}
        for target in plan.targets:
            scored[target.sidecar_dir.name] = adopt_review.ScoredReviewInput(
                sidecar_name=target.sidecar_dir.name,
                scores=[
                    _score("a", 25, maximum=25, critical=True),
                    _score("b", 25, maximum=25),
                ],
            )
        result = run_adopt_review(
            project, rescore=True, apply=True, scored_reviews=scored
        )
        assert result.success, result.report
        sidecar = project / "meridian-a" / "meridian-a.2.review"
        review = adopt_review.Review.model_validate(
            json.loads((sidecar / "_review.json").read_text())
        )
        # total 50 >= 39 but a critical dim forces BLOCK.
        assert review.verdict == adopt_review.Verdict.BLOCK

    def test_empty_scores_rejected(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        plan = adopt_review.build_rescore_plan(project)
        target = plan.targets[0]
        scored = adopt_review.ScoredReviewInput(
            sidecar_name=target.sidecar_dir.name, scores=[]
        )
        with pytest.raises(adopt_review.AdoptReviewError):
            adopt_review.build_scored_review(target, scored)


class TestVerbatimPreservationAndAtomicity:
    def test_review_md_byte_identical_after_rescore(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        before = {}
        for p in project.rglob("review.md"):
            before[p.relative_to(project)] = _digest(p)

        plan = adopt_review.build_rescore_plan(project)
        scored = _scored_map(plan)
        result = run_adopt_review(
            project, rescore=True, apply=True, scored_reviews=scored
        )
        assert result.success, result.report
        for p in project.rglob("review.md"):
            assert before[p.relative_to(project)] == _digest(p)
            assert p.read_text() == FOREIGN_REVIEW_PROSE

    def test_injected_failure_restores_stub_untouched(
        self, tmp_path, monkeypatch
    ):
        project = _build_rescorable_tree(tmp_path)
        plan = adopt_review.build_rescore_plan(project)
        scored = _scored_map(plan)

        import anvil.lib.sidecar as sidecar_mod

        real = sidecar_mod.staged_sidecar

        def failing_staged(final_dir, required_files, **kw):
            cm = real(final_dir, required_files, **kw)
            if final_dir.name == "meridian-c.7.s101":

                class _Boom:
                    def __enter__(self_inner):
                        cm.__enter__()
                        raise RuntimeError("simulated mid-write failure")

                    def __exit__(self_inner, *a):
                        return cm.__exit__(*a)

                return _Boom()
            return cm

        monkeypatch.setattr(adopt_review, "staged_sidecar", failing_staged)

        result = run_adopt_review(
            project, rescore=True, apply=True, scored_reviews=scored
        )
        assert not result.success, result.report
        failed = {n for n, _ in result.apply_result.failed}
        assert "meridian-c.7.s101" in failed

        # The failed sidecar is restored to its ORIGINAL stub state.
        s101 = project / "meridian-c" / "meridian-c.7.s101"
        assert s101.is_dir()
        assert (s101 / "review.md").read_text() == FOREIGN_REVIEW_PROSE
        restored = json.loads((s101 / "_review.json").read_text())
        assert restored["unscored"] is True
        assert restored["scores"] == []
        restored_meta = json.loads((s101 / "_meta.json").read_text())
        assert restored_meta["unscored"] is True
        assert "rescored_from" not in restored_meta
        # No staging / backup dirs survive.
        assert not (
            project / "meridian-c" / ".meridian-c.7.s101.tmp"
        ).exists()
        assert not (
            project / "meridian-c" / ".meridian-c.7.s101.bak"
        ).exists()

    def test_no_leftover_staging_dirs(self, tmp_path):
        project = _build_rescorable_tree(tmp_path)
        plan = adopt_review.build_rescore_plan(project)
        scored = _scored_map(plan)
        run_adopt_review(
            project, rescore=True, apply=True, scored_reviews=scored
        )
        leftovers = [
            p.name
            for p in project.rglob("*")
            if p.is_dir()
            and p.name.startswith(".")
            and (p.name.endswith(".tmp") or p.name.endswith(".bak"))
        ]
        assert leftovers == []


class TestHonestyGuard:
    def test_unresolvable_rubric_skipped_not_guessed(self, tmp_path):
        # No BRIEF + spec.md bodies → rubric cannot be resolved for any
        # stub. Every stub is skipped with a note; nothing is planned.
        project = _build_rescorable_tree(tmp_path, with_brief=False)
        plan = adopt_review.build_rescore_plan(project)
        assert plan.is_noop
        assert plan.targets == []
        # Every foreign stub appears in skipped with the rubric-resolution
        # reason.
        reasons = {name: reason for name, reason in plan.skipped}
        assert "meridian-c.7.enablement" in reasons
        assert "rubric could not be resolved" in reasons[
            "meridian-c.7.enablement"
        ]

    def test_body_filename_route_resolves_rubric(self, tmp_path):
        # No BRIEF, but a memo.md body in the version dir → body-filename
        # route resolves the memo rubric.
        project = build_adopted_review_threads(tmp_path, pre_converted=True)
        # Drop a memo.md body alongside each version dir's spec.md.
        for version in project.rglob("*"):
            if version.is_dir() and version.name in (
                "meridian-c.5",
                "meridian-c.7",
                "meridian-a.2",
            ):
                (version / "memo.md").write_text("# body\n", encoding="utf-8")
        plan = adopt_review.build_rescore_plan(project)
        assert plan.targets
        for target in plan.targets:
            assert target.skill == "memo"
            assert target.skill_source == "body-filename"
            assert target.rubric.id == "anvil-memo-v2"


class TestMixedTree:
    def test_only_stubs_touched_real_review_untouched(self, tmp_path):
        project = build_adopted_review_threads(
            tmp_path, pre_converted=True, with_real_sibling=True
        )
        (project / "BRIEF.md").write_text(_IP_BRIEF, encoding="utf-8")
        audit = project / "meridian-c" / "meridian-c.7.audit"
        before_audit = _digest(audit / "_review.json")

        plan = adopt_review.build_rescore_plan(project)
        scored = _scored_map(plan)
        result = run_adopt_review(
            project, rescore=True, apply=True, scored_reviews=scored
        )
        assert result.success, result.report
        # The real review's _review.json is byte-identical.
        assert _digest(audit / "_review.json") == before_audit
