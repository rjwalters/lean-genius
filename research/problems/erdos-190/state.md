# Current State

**Phase**: ACTIVE_RESEARCH
**Since**: 2026-05-08
**Iteration**: 2

## Current Focus

Add reusable structural lemmas for color conditions on subsets, and clarify
the strength relationship between the Erdős #190 conjecture and the known
result `H(k)^{1/k} → ∞`.

## Active Approach

Three additions to `Erdos190Problem.lean`:

1. `isMonochromatic_subset`: monochromaticity is preserved under subsets.
   Direct destructure-and-restrict.
2. `isRainbow_subset`: rainbowness is preserved under subsets, via
   `Finset.card_image_iff` + `Set.InjOn.mono`. These two helpers form the
   key building blocks for any future monotonicity argument on `H`
   (e.g., `H_monotone : H k ≤ H (k+1)` by truncating canonical (k+1)-APs).
3. `erdos190Conjecture_implies_root_to_infinity`: shows the conjecture
   `H(k)^{1/k}/k → ∞` is strictly stronger than the known result
   `H(k)^{1/k} → ∞` — proves the implication via `(H k)^{1/k} > M·k ≥ M·1 = M`
   for `k ≥ max(K_M, 1)`. This crystallizes the dependency: any progress on
   the conjecture also proves the known result, but not vice versa.

## Blockers

- Build verification deferred (broken `proofs/.lake` symlink).

## Next Action

Iteration 3 candidates:
- `H_monotone : H k ≤ H (k+1)` using `isMonochromatic_subset` /
  `isRainbow_subset`. Truncate canonical (k+1)-AP `f : Fin (k+1) → Fin N` to
  `g : Fin k → Fin N` via `g i := f ⟨i.val, by omega⟩`; AP property + color
  helpers carry through.
- Equivalent reformulation of the conjecture: `H(k) > k^k` eventually
  (for `k` large enough in either direction). Requires `Real.rpow` arithmetic.
- `H_zero : H 0 = 0` (vacuous case via empty Finset image).

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: structural color-subset helpers, conjecture-strength
  reduction
