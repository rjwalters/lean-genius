# Current State

**Phase**: ACTIVE_RESEARCH
**Since**: 2026-05-08
**Iteration**: 8

## Current Focus

Strengthen the structural relationship between Green–Tao (lower bound) and PNT
(upper bound) on `longestPrimeAP(N)`. The previous `pnt_green_tao_bracket`
existentially-quantified the lower bound (∃ M ≤ longestPrimeAP N), making it
trivially satisfiable with M = 0. This iteration makes M a free parameter, so
the bracket statement now carries genuine content from Green–Tao via
monotonicity.

## Active Approach

Factor out two structural lemmas, prove monotonicity, then use it to
strengthen `pnt_green_tao_bracket`:

1. `bddAbove_isPrimeAP : BddAbove {k | IsPrimeAP k N}` — extracted from the
   inline `le_csSup` argument used in `longest_prime_ap_unbounded`. Cleanly
   reusable.
2. `nonempty_isPrimeAP : {k | IsPrimeAP k N}.Nonempty` — `k = 0` is always a
   member because the universally-quantified premises are vacuous.
3. `longest_prime_ap_monotone : N ≤ N' → longestPrimeAP N ≤ longestPrimeAP N'`
   — direct from `csSup_le_csSup` once the set is `BddAbove` and `Nonempty`.
4. Strengthened `pnt_green_tao_bracket`:
   `∀ ε > 0, ∀ M, ∃ N₀, ∀ N ≥ N₀, M ≤ longestPrimeAP N ∧ longestPrimeAP N ≤ (1+ε)·log N`.
   Proof: pick `N₁` from PNT axiom, `N_M` from Green–Tao, take `N₀ = max N₁ N_M`,
   apply `le_csSup` at `N_M` then `longest_prime_ap_monotone`.

## Blockers

- Build verification deferred (broken `proofs/.lake` symlink in main repo
  forces a fresh Mathlib clone). Marked PR as build pending per convention.

## Next Action

Iteration 9 candidates:
- Add concrete `prime_ap_8` (d=210, length-8 starting at 199) and `prime_ap_10`
  (d=210, length-10 ending at 2089) to push the explicit witness from k=7 to k=10.
- Prove a *quantitative* lower bound on the smallest N containing a length-k
  prime AP: combine `ap_difference_primorial` with primorial growth.
- Replace inline proof in `longest_prime_ap_unbounded` with the factored
  `bddAbove_isPrimeAP` lemma (cleanup).

## Attempt Counts

- Total attempts: 8 (per merged PR history)
- Current approach attempts: 1
- Approaches tried: structural-bracket strengthening, monotonicity
