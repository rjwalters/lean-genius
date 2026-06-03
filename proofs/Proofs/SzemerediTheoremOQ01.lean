/-
# Kelley–Meka Quantitative Bound for 3-AP-Free Sets

The Kelley–Meka 2023 breakthrough bound
`r_3(N) ≤ N · exp(-c · (log N)^(1/12))`, stated against Mathlib's
`rothNumberNat` (the maximum size of a 3-AP-free subset of
`{0, …, N-1}`).

## Status

**Axiomatized.** The Kelley–Meka proof relies on sifted Fourier analysis
over Bohr sets and a `U^3`-flavored inverse theorem; none of this
infrastructure is in Mathlib 4.26. The qualitative Roth direction is
already proved unconditionally elsewhere in the gallery, so this entry
contributes the quantitative shape of the current best bound rather than
duplicating the existing Mathlib chain.

## Why this is honestly stronger than the existing chain

Mathlib's `roth_3ap_theorem_nat` is driven by `cornersTheoremBound`,
which depends on `SzemerediRegularity.bound` — a tower-type
exponential. Inverting that bound yields a density rate in the
`log*` (iterated logarithm) class, far weaker than Kelley–Meka's
quasi-polynomial `exp(-c (log N)^(1/12))`. The gap between the two
rates is exactly the reason this entry is its own axiom rather than a
corollary of existing Mathlib work.

## Companion / sibling

A Salem–Spencer quantitative Roth statement was investigated in
`research/problems/szemeredi-theorem-oq-01/` Session 2 and ruled out:
deriving `O(N / log log N)` from `cornersTheoremBound` is not possible
given the tower-type rate. That Approach B is tracked as the
recommended sibling slug `szemeredi-theorem-oq-01-incomplete-01`,
BLOCKED on the same Bohr-set / sifted-Fourier / `U^3` infrastructure.

## Reference

Kelley, Zander and Meka, Raghu. *Strong bounds for 3-progressions*.
FOCS 2023 (full version in Annals of Mathematics, 2024).
-/

import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SzemerediTheoremOQ01

open Real

/-- **Kelley–Meka quantitative bound** (axiom).

There exists an absolute constant `c > 0` such that for all sufficiently
large `N`, every 3-AP-free subset of `{0, …, N-1}` has size at most
`N · exp(-c (log N)^(1/12))`.

Stated against Mathlib's `rothNumberNat`, which is exactly the maximum
size of a 3-AP-free subset of `{0, …, N-1}`. The exponent `1/12` is the
Kelley–Meka value as it appears in their 2023 paper; subsequent
improvements may push the exponent up but are not in scope here. -/
axiom kelley_meka_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (rothNumberNat N : ℝ) ≤
        (N : ℝ) * Real.exp (-(c * Real.log (N : ℝ) ^ ((1 : ℝ) / 12)))

/-- **Density form of the Kelley–Meka bound** (non-axiomatic corollary).

Under `kelley_meka_bound`, the density `r_3(N) / N` is bounded above by
`exp(-c (log N)^(1/12))` once `N ≥ max N₀ 1`. This is the form most
commonly cited in surveys and is what makes the Kelley–Meka rate
quasi-polynomial: the right-hand side is `1/exp(c (log N)^(1/12))`, which
beats every `1/(log N)^k`. -/
theorem rothNumberNat_density_le_kelley_meka :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (rothNumberNat N : ℝ) / N ≤
        Real.exp (-(c * Real.log (N : ℝ) ^ ((1 : ℝ) / 12))) := by
  obtain ⟨c, hc, N₀, hbound⟩ := kelley_meka_bound
  refine ⟨c, hc, max N₀ 1, ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := (le_max_left N₀ 1).trans hN
  have hN1 : 1 ≤ N := (le_max_right N₀ 1).trans hN
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_succ_le hN1
  have hb := hbound N hN₀
  rw [div_le_iff₀ hN_pos, mul_comm]
  exact hb

end SzemerediTheoremOQ01
