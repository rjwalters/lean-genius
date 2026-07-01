/-
# The Unweighted n-Variable AM–GM Inequality and its Equality Case

This file specializes the parent development
(`Proofs.JensenInequalityOQ01`, gallery entry `jensen-inequality-oq-01`), which established the
sharp **weighted** arithmetic–geometric mean inequality and its equality characterization, to the
classical **unweighted** `n`-variable case obtained with uniform weights `1/|s|`:

    ⁿ√(x₁⋯xₙ)  ≤  (x₁ + ⋯ + xₙ)/n,     with equality  ⇔  x₁ = ⋯ = xₙ.

The bridge from the weighted statement to this one is purely algebraic: the uniform weight family
`w i = 1/|s|` is strictly positive and sums to `1`, the weighted geometric mean
`∏ zᵢ^{1/n}` collapses to the single `n`-th root `(∏ zᵢ)^{1/n}` via `Real.finset_prod_rpow`, and the
weighted arithmetic mean `∑ (1/n)·zᵢ` becomes `(∑ zᵢ)/n`. No new analysis is required — everything
rides on the parent's `weighted_amgm_le`, `weighted_amgm_eq_iff`, and `weighted_amgm_lt_of_ne`.

## Main results

* `unweighted_amgm_le` — the unweighted AM–GM inequality `(∏ zᵢ)^{1/|s|} ≤ (∑ zᵢ)/|s|`.
* `unweighted_amgm_eq_iff` — equality `(∏ zᵢ)^{1/|s|} = (∑ zᵢ)/|s|` holds **iff** all `zᵢ` are equal.
* `unweighted_amgm_lt_of_ne` — if two of the (positive) values differ, the inequality is strict.
* `amgm_fin_le`, `amgm_fin_eq_iff` — the concrete `Fin n` restatements matching the classical
  `ⁿ√(x₁⋯xₙ) ≤ (x₁+⋯+xₙ)/n` form.

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib
import Proofs.JensenInequalityOQ01

open Finset Real

namespace UnweightedAMGM

variable {ι : Type*} {s : Finset ι} {z : ι → ℝ}

/-- The uniform weights `1/|s|` sum to `1` on a nonempty finite index set. -/
private theorem sum_uniform (hs : s.Nonempty) :
    ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hs).ne'
  rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]

/-- **Unweighted AM–GM inequality.** For nonnegative data indexed by a nonempty finite set, the
geometric mean `(∏ zᵢ)^{1/|s|}` is at most the arithmetic mean `(∑ zᵢ)/|s|`. This is the uniform-weight
specialization of the parent's `weighted_amgm_le`. -/
theorem unweighted_amgm_le (hs : s.Nonempty) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i) ^ (s.card : ℝ)⁻¹ ≤ (∑ i ∈ s, z i) / s.card := by
  have hcpos : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hw : ∀ i ∈ s, (0 : ℝ) ≤ (s.card : ℝ)⁻¹ := fun _ _ => (inv_pos.mpr hcpos).le
  have hle := weighted_amgm_le hw (sum_uniform hs) hz
  rw [Real.finset_prod_rpow s z hz, ← Finset.mul_sum] at hle
  rwa [div_eq_inv_mul]

/-- **Equality case of unweighted AM–GM.** With nonnegative data on a nonempty finite index set,
the geometric and arithmetic means coincide **iff all the data are equal**. Uniform-weight
specialization of the parent's `weighted_amgm_eq_iff`. -/
theorem unweighted_amgm_eq_iff (hs : s.Nonempty) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i) ^ (s.card : ℝ)⁻¹ = (∑ i ∈ s, z i) / s.card
      ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  have hcpos : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hw : ∀ i ∈ s, (0 : ℝ) < (s.card : ℝ)⁻¹ := fun _ _ => inv_pos.mpr hcpos
  have h := weighted_amgm_eq_iff hw (sum_uniform hs) hz
  rwa [Real.finset_prod_rpow s z hz, ← Finset.mul_sum, ← div_eq_inv_mul] at h

/-- **Strict unweighted AM–GM.** With strictly positive data on a nonempty finite index set, if two
of the values differ then the geometric mean is *strictly* below the arithmetic mean. Uniform-weight
specialization of the parent's `weighted_amgm_lt_of_ne`. -/
theorem unweighted_amgm_lt_of_ne (hs : s.Nonempty) (hz : ∀ i ∈ s, 0 < z i)
    (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    (∏ i ∈ s, z i) ^ (s.card : ℝ)⁻¹ < (∑ i ∈ s, z i) / s.card := by
  have hcpos : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hw : ∀ i ∈ s, (0 : ℝ) < (s.card : ℝ)⁻¹ := fun _ _ => inv_pos.mpr hcpos
  have hlt := weighted_amgm_lt_of_ne hw (sum_uniform hs) hz hne
  rw [Real.finset_prod_rpow s z (fun i hi => (hz i hi).le), ← Finset.mul_sum,
    ← div_eq_inv_mul] at hlt
  exact hlt

/-! ## Concrete `Fin n` restatements

These package the results in the familiar `ⁿ√(x₁⋯xₙ) ≤ (x₁+⋯+xₙ)/n` shape. -/

/-- **Classical `n`-variable AM–GM inequality.** For `n > 0` nonnegative reals,
`(∏ zᵢ)^{1/n} ≤ (∑ zᵢ)/n`. -/
theorem amgm_fin_le {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i, z i) ^ (n : ℝ)⁻¹ ≤ (∑ i, z i) / n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have h := unweighted_amgm_le (s := (Finset.univ : Finset (Fin n)))
    Finset.univ_nonempty (fun i _ => hz i)
  rwa [hcard] at h

/-- **Classical `n`-variable AM–GM equality case.** For `n > 0` nonnegative reals, equality
`(∏ zᵢ)^{1/n} = (∑ zᵢ)/n` holds **iff all the values are equal**. -/
theorem amgm_fin_eq_iff {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i, z i) ^ (n : ℝ)⁻¹ = (∑ i, z i) / n ↔ ∀ j k, z j = z k := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have h := unweighted_amgm_eq_iff (s := (Finset.univ : Finset (Fin n)))
    Finset.univ_nonempty (fun i _ => hz i)
  rw [hcard] at h
  simpa using h

end UnweightedAMGM
