# Research State: erdos-43-oq-05

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-03-29T23:39:51-07:00
**Iteration**: 2

## Current Focus
Question status reassessment in light of the current Lean source.

## OBSERVE finding (2026-06-09, researcher-1)

**The OQ-05 question is "Can the five `sorry` counting lemmas be proved using Mathlib's `Finset.card` API?"**

The current `proofs/Proofs/Erdos43Problem.lean` contains the five named counting
theorems with **no `sorry`s** — they are already fully discharged via `Finset.card`,
`Finset.card_image_of_injOn`, `Finset.card_le_card`, and the `Finset.card_offDiag`
identity. The five theorems are:

1. `sidon_pair_bound` (line 84) — `A.card.choose 2 ≤ N` for Sidon `A ⊆ {1..N}`
2. `disjoint_diff_combined_bound` (line 123) — combined bound from disjoint differences
3. `tao_equal_size_bound` (line 203) — Tao's equal-size variant bound
4. `sidon_diff_injective` (line 227) — injectivity of difference map on Sidon offDiag
5. `sidon_diff_count` (line 250) — `|diffSet A| = |A|² - |A| + 1`

So the *answer* to OQ-05 is **YES**, and the proofs are already on disk.

## Caveat — file does NOT build at HEAD under Mathlib v4.26.0

Attempted a build at HEAD: the file produces 13+ errors due to upstream Mathlib churn
(rename `Finset.card_offDiag` → `Finset.offDiag_card` with a different RHS form
`n*n - n` rather than `n * (n - 1)`; broken `omega`/`linarith` after Real.sqrt API
changes; a `subst` failure in `sidon_diff_injective`; a `simp` no-op in
`sidon_diff_count`). These are routine v4.26.0 compatibility breaks identical in shape
to the ones I just fixed for Erdos406Problem.lean in PR #22729.

I did NOT ship a repair PR for Erdos43Problem.lean in this iteration — the v4.26.0
fixes are mechanical-but-multi-step (~13 sites including `offDiag_card`'s changed RHS,
which propagates through omega goals), and an in-progress partial fix would leave the
file in worse shape than untouched. A future iteration should:
1. Globally rename `Finset.card_offDiag` → `Finset.offDiag_card`
2. After the rename, adjust the goals to match the new `n*n - n` form
   (insert `Nat.mul_sub_one` or `Nat.sub_one_mul` rewrites)
3. Investigate the `subst 'b' occurs at` failure at line 263 (likely a Lean elaboration
   ordering change)

## Active Approach
None — releasing claim; OBSERVE-only iteration with documented finding.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
File-level Mathlib v4.26.0 compatibility (not a math blocker; routine API churn).

## Next Action
Future iteration: do the v4.26.0 build repair on `Erdos43Problem.lean` following the
pattern from PR #22729 (Erdos406Problem.lean). Once the file builds, the OQ-05
question can be marked resolved with status `completed`.
