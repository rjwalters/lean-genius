# Research State: erdos-53-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T17:33:19-07:00
**Iteration**: 4

## Current Focus
Quadratic additive lower bound landed: |subsetSums A| >= n(n+1)/2+1 for ALL positive sets (Erdős max-removal chain), plus sumsOrProducts quadratic/superlinear corollaries. theoremCount 11->19 in Erdos53WIP01.lean, still 0 axioms.

## Active Approach
Elementary structural formalization of subset-sum/product sets; Chang deep theorem stays documented.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Remaining deep crux: Chang (|A|^k for arbitrary large sets, k>=2) — needs Freiman/Plünnecke machinery, out of scope. Possible elementary rungs: extend the chain bound to sets allowing negative elements (positivity currently required for the total-sum upper bound), or product-side analogue |subsetProducts| for sets of integers > 1 via monotone chain on log.

## Status (researcher-1, 2026-07-23) — product-side chain landed

The "product-side analogue" rung from Next Action is DONE:
`subsetProducts_card_quadratic` — |subsetProducts A| >= n(n+1)/2 for ARBITRARY
sets of integers > 1 (no primality). Moves the subsetProducts frontier from
"prime sets only" (2^n − 1) to all sets of elements >= 2. Same max-removal
chain as the additive bound, transposed division-free: fresh values written as
Π(A.erase a) (never P/a), comparisons via cancellation on Π(A.erase a)·a = ΠA
(mul_left_cancel₀ / lt_of_mul_lt_mul_right), subset-product ≤ full-product via
prod_dvd_prod_of_subset + Int.le_of_dvd (ℤ's multiplicative monoid is not
ordered — sum monotonicity has no direct analogue). The >1 hypothesis is
essential: 1 ∈ A collides Π(A.erase 1) with ΠA (mirror of 0 ∈ A additively).
Sharp for {2, 4, ..., 2^n} (products = 2^[1..n(n+1)/2], remark only).
Helpers: prod_mem_subsetProducts, prod_erase_mem_subsetProducts,
mem_subsetProducts_le_prod. theoremCount 19->25, still 0 axioms.

Both sides of Problem 53 are now individually quadratic on their natural
domains; the remaining content is exactly Chang (sum-product tension), deep.

## Next Action (updated)
Chang |A|^k arbitrary sets (deep, Freiman/Plünnecke — out of elementary
scope). Thin rung left: negative elements in the ADDITIVE chain (positivity
only used for the total-sum upper bound; max-removal still works if 0 ∉ A?
— needs care, subset sums can collide across sign). Elementary vein otherwise
SATURATED.

## Status (researcher-1, 2026-07-23, iteration 2) — negative-elements rung REFUTED; node closed

The last thin rung ("negative elements in the additive chain") is now CLOSED
with a machine-checked refutation, not a note:

- `subsetSums_quadratic_fails_of_negative`: for EVERY n >= 2 the witness
  {-1, 1, 2, ..., n-1} (n distinct nonzero integers) has
  2*|subsetSums A| < n(n+1) + 2 — the quadratic bound FAILS. All subset sums
  lie in [-1, (n-1)n/2] (the -1 lowers by at most 1; the positive part is
  capped by its total), so at most (n-1)n/2 + 2 values vs the triangular
  demand n(n+1)/2 + 1: a margin growing linearly (n-1). So positivity cannot
  be weakened to nonzero — the failure is structural (additive cancellation),
  not a small-case accident.
- Helpers: `two_mul_sum_Icc_id` (Gauss, Icc form);
  `subsetSums_pair_neg_card` ({1,-1} has exactly 3 subset sums, by decide).
- All #print axioms = [propext, Classical.choice, Quot.sound]. theoremCount
  25 -> 28, still 0 axioms/sorries.

## Final state

Elementary vein FULLY SATURATED and now definitively fenced:
- additive side quadratic for positive sets (sharp), multiplicative side
  quadratic for sets > 1 (sharp), prime family exponential for all k,
  parity refinement, and the signed extension REFUTED.
- Remaining content is exactly Chang 2003 (|A|^k for arbitrary large sets,
  Freiman/Plünnecke + multiplicative energy) — deep, documented, out of
  elementary scope. Node complete.
