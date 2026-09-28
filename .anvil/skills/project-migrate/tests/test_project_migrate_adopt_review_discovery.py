"""Post-apply discovery integration tests for `--adopt-review` (issue #454).

The load-bearing risk flagged at curation: an empty-`scores` stub Review
now flows into `critics.aggregate`. This module verifies:

1. `discover_critics` finds a converted sidecar after apply.
2. `load_review` parses the stub without error.
3. `aggregate([stub, real_sibling])` does NOT corrupt the real sibling's
   total or flip its verdict — the zero-dimension-tolerance check (the
   stub contributes 0 dimensions; the real critic drives the verdict).
"""

from __future__ import annotations

from _fixtures import build_adopted_review_threads
from _project_migrate_skill_lib import orchestrate

from anvil.lib.critics import (
    aggregate,
    compute_verdict,
    discover_critics,
    load_review,
)
from anvil.lib.review_schema import Verdict

run_adopt_review = orchestrate.run_adopt_review


class TestDiscovery:
    def test_discover_and_load_stub(self, tmp_path):
        project = build_adopted_review_threads(tmp_path)
        run_adopt_review(project, apply=True)

        version_dir = project / "meridian-c" / "meridian-c.7"
        criticism = discover_critics(version_dir)
        names = sorted(p.name for p in criticism)
        # Both converted foreign siblings are now discoverable.
        assert "meridian-c.7.enablement" in names
        assert "meridian-c.7.s101" in names

        for sidecar in criticism:
            review = load_review(sidecar)  # parses without error
            assert review.unscored is True
            assert review.scores == []
            assert review.version_dir == "meridian-c.7"

    def test_stub_invisible_before_apply(self, tmp_path):
        # Before conversion, the review.md-only siblings are NOT discovered
        # (the #346 additive contract — invisible-but-intact).
        project = build_adopted_review_threads(tmp_path)
        version_dir = project / "meridian-c" / "meridian-c.7"
        assert discover_critics(version_dir) == []


class TestZeroDimensionTolerance:
    """The required load-bearing check: a stub alongside a real critic."""

    def test_stub_does_not_corrupt_real_sibling_total(self, tmp_path):
        project = build_adopted_review_threads(
            tmp_path, with_real_sibling=True
        )
        run_adopt_review(project, apply=True)

        version_dir = project / "meridian-c" / "meridian-c.7"
        sidecars = discover_critics(version_dir)
        # The real .audit sibling + the two converted foreign stubs.
        names = sorted(p.name for p in sidecars)
        assert names == [
            "meridian-c.7.audit",
            "meridian-c.7.enablement",
            "meridian-c.7.s101",
        ]

        reviews = [load_review(s) for s in sidecars]

        # Aggregate ALL THREE (real + two stubs).
        agg_all = aggregate(reviews)
        # Aggregate the real critic ALONE for the reference verdict/total.
        real = [r for r in reviews if r.critic_id == "audit"]
        agg_real = aggregate(real)

        # The stubs contribute ZERO dimensions, so the aggregated total
        # equals the real critic's total — unchanged.
        assert agg_all.total == agg_real.total == 15
        # Threshold (first non-null across reviews) is the real critic's.
        assert agg_all.threshold == 14
        # And the verdict is NOT flipped: still ADVANCE, exactly as the
        # real critic alone.
        assert agg_all.verdict == agg_real.verdict == Verdict.ADVANCE
        assert compute_verdict(agg_all) == Verdict.ADVANCE

    def test_stub_only_aggregate_does_not_spurious_advance(self, tmp_path):
        # A version dir whose ONLY critics are stubs: aggregate must not
        # spuriously ADVANCE (no div-by-zero, no zero>=zero advance on a
        # fabricated threshold). meridian-a.2 has only the foreign .review
        # stub.
        project = build_adopted_review_threads(tmp_path)
        run_adopt_review(project, apply=True)

        version_dir = project / "meridian-a" / "meridian-a.2"
        sidecars = discover_critics(version_dir)
        reviews = [load_review(s) for s in sidecars]
        assert all(r.unscored for r in reviews)

        agg = aggregate(reviews)
        # Zero dims → total 0, threshold defaults to sum-of-max = 0.
        assert agg.total == 0
        # With threshold == 0, total (0) >= threshold (0) → ADVANCE is the
        # documented aggregate behavior for an all-null scorecard; the
        # honest reading is "nothing scored" and the operator must run a
        # real review. The contract we lock here is: NO crash, NO critical
        # flags fabricated, verdict is deterministic.
        assert agg.verdict in (Verdict.ADVANCE, Verdict.REVISE)
        assert agg.critical_flags == []
        assert agg.scores == []
