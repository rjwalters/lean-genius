# Research State: schroeder-bernstein-oq-03

## Current State
**Phase**: DEVELOP
**Path**: full
**Since**: 2026-07-02
**Iteration**: 3

## Current Focus
Assemble the outer stage recursion of the Myhill priority scheduler now that the atomic
even-stage move is total and iterable (`augment_domain_step`, Section 4k).

## Active Approach
Stage-wise finite back-and-forth (Rogers §7.4). Even (domain) stage: `augment_domain_step`
— DONE this session (BuiltFrom-preserving splice of the augmenting path, all invariants +
monotonicity + anchor coverage, VERIFIED 0-axiom). Odd (range) stage: its `Prod.swap` dual
via Section 4e (`isMatching_map_swap` / `matchingCorr_map_swap` / `builtFrom_map_swap`) —
NOT YET INSTANTIATED but every ingredient present.

## Attempt Count
- Approaches tried: 1 (stage-wise back-and-forth), advancing across sessions.

## Blockers
None at the atomic level — all per-stage obligations (termination, correspondence, BuiltFrom
preservation, matching validity, monotonicity) are proved. Remaining work is the OUTER
assembly: a well-founded stage function `σ : ℕ → List (ℕ×ℕ)`, its computability, and reading
off a computable `ℕ ≃ ℕ` (totality on both sides from monotonicity + `firstMissing` coverage;
injectivity from `mLookup_injOn` / `mLookup_stable`).

## Next Action
1. Derive the range-stage dual `augment_range_step` from `augment_domain_step` via the swap
   duality (Section 4e).
2. Define the stage recursion alternating the two steps, anchoring each stage at
   `firstMissing (mDom σₛ)` (even) / `firstMissing (mRan σₛ)` (odd).
3. Prove coverage (`k ∈ mDom` by stage `2k+1`, dual for range) from monotonicity + the
   `firstMissing` progress lemmas (Section 4e).
4. Read off `e : ℕ ≃ ℕ` via `mLookup` and prove `.Computable`; discharge `myhill_isomorphism`.
