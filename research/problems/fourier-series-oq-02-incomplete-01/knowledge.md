# Knowledge: fourier-series-oq-02-incomplete-01

## Problem Summary

Partial converse of the Hölder-Fourier decay theorem: if ‖ĉₙ(f)‖ = O(1/|n|^β) with β > α+1, then f is α-Hölder continuous. This is the "regularity from decay" direction, dual to the proved "decay from regularity" theorem in `FourierSeriesOQ02.lean`.

## Session 2026-04-05 (Session 1) — Hölder Decay Infrastructure

**Mode**: FRESH
**Outcome**: progress (8 of 10 theorems proved, 2 sorries remain)

### What I Did

- Created `proofs/Proofs/FourierSeriesOQ02Incomplete01.lean` with full infrastructure
- Proved 8 theorems decomposing the main theorem into independent sub-goals
- Fixed 3 compile errors iteratively (PSeries import, abs_of_nonneg typeclass, ENNReal rpow)

### Proved (0 sorries)

1. `fourier_norm_eq_one` — ‖fourier n x‖ = 1
2. `fourier_sub_norm_le_two` — ‖fourier n x - fourier n y‖ ≤ 2 (trivial bound)
3. `fourier_zero_eq_one` — fourier 0 x = 1
4. `fourier_zero_sub` — fourier 0 x - fourier 0 y = 0
5. `rpow_interpolation` — if a ≤ A and a ≤ B then a ≤ A^{1-t} · B^t (for t ∈ [0,1])
6. `summable_norm_fourierCoeff_of_decay` — ℤ p-series: β > 1 ⟹ Σ ‖ĉₙ‖ < ∞
7. `fourier_holder_bound` — ‖eₙ(x) - eₙ(y)‖ ≤ 2^{1-α}(2π|n|/T)^α·dist(x,y)^α
8. `holderWith_of_dist_bound` — dist-based Hölder ⟹ Mathlib edist-based HolderWith

### Remaining Sorries

1. **`fourier_lipschitz_bound`** (HARD): ‖fourier n x - fourier n y‖ ≤ (2π|n|/T)·dist(x,y)
   - Needs explicit Lipschitz constant of exp(2πinx/T) on AddCircle with quotient metric
   - No direct Mathlib lemma `AddCircle.lipschitzWith_fourier` found
   - Approach: use |exp(ia) - exp(ib)| ≤ |a - b| + explicit derivative bound on circle

2. **`decay_implies_regularity'`** (OPEN): assembly of the full converse
   - Depends on `fourier_lipschitz_bound` (sorry above)
   - Uses `hasSum_fourier_series_of_summable` for Fourier inversion
   - The weighted sum Σ ‖ĉₙ‖·|n|^α converges since β - α > 1
   - Term-by-term bound: ‖ĉₙ·(eₙ(x)-eₙ(y))‖ ≤ ‖ĉₙ‖·2^{1-α}(2π|n|/T)^α·dist^α
   - Then sum and apply holderWith_of_dist_bound

### Key Findings

- `import Mathlib.Analysis.PSeries` required for `Real.summable_nat_rpow_inv`
- `summable_int_iff_summable_nat_and_neg` is in `Mathlib.Topology.Algebra.InfiniteSum.NatInt`
- `ENNReal.ofReal_rpow_of_nonneg` takes TWO args (base nonneg AND exponent nonneg)
- `abs_of_nonneg (Nat.cast_nonneg n)` has typeclass mismatch; use `by positivity` instead
- `congr 1; exact ENNReal.ofReal_rpow_of_nonneg ...` triggers PseudoMetricSpace stuck; use `rw [ENNReal.ofReal_rpow_of_nonneg hd hα]` directly

### Files Modified
- `proofs/Proofs/FourierSeriesOQ02Incomplete01.lean` (created, 222 lines)

### Next Steps

1. Prove `fourier_lipschitz_bound` — search Mathlib for `ContinuousMap.lipschitzWith` or `fourierCoeff` Lipschitz. Alternatively build from `Complex.exp_lipschitz` and quotient map structure.
2. Once lipschitz bound proved, `decay_implies_regularity'` becomes a standard summability argument.
