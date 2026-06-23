# S15 — Mathlib API drift fix: `Metric.mem_closedBall_zero_iff` → `mem_closedBall_zero_iff`

**Date:** 2026-05-09
**Researcher:** researcher-3
**PR:** #17654
**Outcome:** Drift fix; build pending.

## Problem

The S13 retraction-reduction body (`theorem brouwer_fpt`, PR #17575)
and S14 helper-lemma proof (`exists_continuous_proj_convex`, PR
#17601) both referenced `Metric.mem_closedBall_zero_iff` to convert
`x ∈ Metric.closedBall 0 r` ↔ `‖x‖ ≤ r` inside the elementwise
rescaling step.

The build of the S14 file failed (see
`.loom/logs/researcher-3-s14-build.log`):

```
error: Proofs/SchauderFixedPointOQ03OQ01.lean:210:8:
  Unknown identifier `Metric.mem_closedBall_zero_iff`
error: Proofs/SchauderFixedPointOQ03OQ01.lean:228:8:
  Unknown identifier `Metric.mem_closedBall_zero_iff`
```

## Resolution

Verified via direct GitHub-API inspection of the Mathlib source at
the v4.26.0 tag (the rev pinned in
`proofs/lake-manifest.json`):

```
$ gh api repos/leanprover-community/mathlib4/contents/\
    Mathlib/Analysis/Normed/Group/Basic.lean?ref=v4.26.0 \
    --jq .content | base64 -d | grep -nE 'mem_closedBall_zero|@\[to_additive.*mem_closedBall' -A 1

634-@[to_additive mem_closedBall_iff_norm]
635-theorem mem_closedBall_iff_norm'' : b ∈ closedBall a r ↔ ‖b / a‖ ≤ r := …
638-@[to_additive]
639-theorem mem_closedBall_one_iff : a ∈ closedBall (1 : E) r ↔ ‖a‖ ≤ r := …
```

The `@[to_additive]` attribute on `mem_closedBall_one_iff` generates
`mem_closedBall_zero_iff` in the **root** namespace (NOT `Metric.`).
The 4 call sites in `SchauderFixedPointOQ03OQ01.lean` (lines 308, 312,
326, 330) already use `Metric.closedBall` (with the prefix) for the
closed-ball *type*; only the membership iff *lemma* had the spurious
prefix.

Net diff: 4 single-token replacements, no semantic change.

## Verification of the fix

The 4 call sites use the lemma in the standard
`x ∈ Metric.closedBall 0 r ↔ ‖x‖ ≤ r` direction:

```lean
have hσ_in_B : ∀ x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
    R • ((x : EuclideanSpace ℝ (Fin n)))
      ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
  intro x
  rw [mem_closedBall_zero_iff, norm_smul,                  -- target: ‖R • x‖ ≤ R
      Real.norm_of_nonneg hR_pos.le]
  have hx_le : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
    have hx := x.property                                  -- x ∈ closedBall 0 1
    rwa [mem_closedBall_zero_iff] at hx                    -- → ‖x‖ ≤ 1
  …
```

The lemma signature (`a ∈ closedBall (0 : E) r ↔ ‖a‖ ≤ r`) matches
the call-site usage; the rewrite direction is correct.

## Net file effect

| Field          | Before | After |
|----------------|--------|-------|
| Sorries (code) | 0      | 0     |
| Axiom count    | 2      | 2     |
| Line count     | 766    | 766   |
| Lines changed  | —      | 4     |

The two remaining axioms are:

- `axiom brouwer_unit_ball` (closed-unit-ball Brouwer FPT)
- `axiom approx_selection_exists` (Cellina–Browder graph approximate
  selections for upper-hemicontinuous maps with convex values)

## Build verification

Docker build (`./proofs/scripts/docker-build.sh
Proofs.SchauderFixedPointOQ03OQ01`) kicked off at PR submission time;
log file `.loom/logs/researcher-3-s15-build.log`. If green, the
file is end-to-end sorry-free at `axiomCount = 2` and meta.json drift
can be synced (`sorries: 1 → 0`, `lineCount: 668 → 766`).

## Lessons

This drift was introduced in S13 (the body landing) and went unnoticed
through S14 because the build runs took longer than the iteration
cadence. The pattern (deployer auto-merging "build pending" PRs; cf.
`feedback_docstring_only_merges_mask_type_errors.md` and
`feedback_basel_oq03_iter12_three_fixes.md`) means name-drift bugs in
freshly-merged proof bodies stay latent until a researcher next reads
the build log carefully.

The `Metric.` vs root-namespace distinction is recurrent in
Mathlib4: `Metric.closedBall` (the type) lives in the `Metric`
namespace, but normed-group membership iffs (e.g. `mem_closedBall_zero_iff`,
`mem_closedBall_one_iff`) sit at root via `@[to_additive]` from
`Mathlib.Analysis.Normed.Group.Basic`. When `import
Mathlib.Topology.MetricSpace.Basic` is in play but the membership
lemma is multiplicative-additive translated, the prefix is wrong.
