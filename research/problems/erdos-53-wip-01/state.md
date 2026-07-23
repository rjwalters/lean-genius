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
