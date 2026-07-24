# Research State: erdos-30-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24T00:00:00-07:00
**Iteration**: 9

## Current Focus
Reduction layer LANDED (iteration 9, same session): the $1000 `N^ε`
conjecture's scaffolding is now formal. `Erdos30ConjectureAt ε` (single-
exponent two-sided bound), `RequiredLowerBound ε` (Singer side, mirroring
`RequiredUpperBound`), exponent-monotonicity for both families,
`erdos30Conjecture_of_bounds` (the two one-sided families assemble the
conjecture), `erdos30Conjecture_of_stronger` (O(1) ⟹ N^ε), and
`erdos30ConjectureAt_half` — the proved bracket settles the ε = 1/2
instance unconditionally (C = √2), so the open content lives strictly
below ε = 1/2 (below 1/4 after Erdős–Turán). Builds on iteration 8's
bracket `sidonNumber_sqrt_bracket : √N/4 ≤ h(N) ≤ √(2N)+1`.

## Active Approach
Erdős–Turán construction proof = base-2p digit separation (`etMap_add_eq`,
residues < p never carry) + quadratic uniqueness over 𝔽_p
(`pair_eq_of_sum_sq`, `linear_combination` workhorse; 2 invertible for
p > 2). Exact table h(0..28) stands via the residue-class ladder
(h(10)/h(21) parity, h(15) mod-3, h(28) mod-4) + span dichotomy searches.

## Attempt Count
- Total attempts: 9 sessions
- Current approach attempts: 1 (conjecture reduction layer — landed)
- Approaches tried: parity wall, mod-3 class count, span dichotomy,
  mod-4 double count, Erdős–Turán modular construction

## Blockers
h(29..33) wall: perfect ruler no longer forced (28 diffs in {1,…,N} miss
N−28 values); span dichotomy returns but the span-N branch needs per-N
nonexistence with C(N−1,6)-scale kernel searches (~376k at N=29). Mod-4
alone checked INSUFFICIENT at N=29 (a {4,2,1,1} arrangement with the missing
value ≡ 2 mod 4 survives). Elementary layer near-saturated.

## Next Action
Conjecture reduction scaffolding DONE (iteration 9) — the conjecture
itself is now cleanly `∀ ε > 0, RequiredUpperBound ε ∧ RequiredLowerBound ε`
up to assembly, with ε = 1/2 settled. Remaining targets are all DEEP:
sharp constants (Singer projective-plane lower `(1−o(1))√N`, which would
feed `RequiredLowerBound` for every ε; Lindström/BFR upper
`√N + N^{1/4} + 1`, which would feed `RequiredUpperBound (1/4)`), or the
h(29..33) table wall (new invariant — mod-3×mod-4 combination / endpoint
sum-collision pruning — or a ~376k kernel search). Treat elementary vein
as SATURATED.
