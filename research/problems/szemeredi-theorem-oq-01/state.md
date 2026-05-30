# Research State: szemeredi-theorem-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-05-30 (was OBSERVE since 2026-04-05)
**Iteration**: 2

## Current Focus
Choose between Approach A (axiomatize) and Approach B (Salem-Spencer
quantitative). Pending Mathlib audit of `cornersTheoremBound`'s
constant structure (see knowledge.md, open question 1).

## Active Approach
**B (recommended)** — quantitative Roth via Mathlib `cornersTheoremBound`,
extract explicit `O(N / log log N)` constants. ~150-300 lines if
`cornersTheoremBound` already exposes the constants; falls back to
Approach A (axiomatize Kelley-Meka) otherwise.

## Attempt Count
- Total attempts: 0 (survey only)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None. Pending decision is informational, not a true blocker.

## Next Action
Read `Mathlib.Combinatorics.Additive.Corner.Roth` and inspect
`cornersTheoremBound` to determine the actual quantitative form of
Mathlib's Roth bound. Branch decision tree:
- If `cornersTheoremBound` already gives explicit `O(N / log log N)`
  constants: commit to Approach B, build a `SzemerediTheoremOQ01.lean`
  with `r_3_quantitative_bound` as a theorem (~50-150 lines).
- If `cornersTheoremBound` is tower-type / opaque: commit to Approach A
  for this problem; axiomatize the Kelley-Meka statement (~30 lines).
  Spin off Approach B into a sibling problem
  `szemeredi-theorem-oq-01-incomplete-01`.

See knowledge.md for the full survey and Mathlib gap inventory.
