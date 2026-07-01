/-
# The Unweighted n-Variable AM–GM Equality Case

This file extends the parent entry
(`Proofs.JensenInequalityOQ01`, "The Equality Case of Strict Jensen, and the Sharp
Weighted AM–GM Equality") from the two-variable instance `amgm_two_eq_iff` to the full
**unweighted `n`-variable** arithmetic–geometric mean equality case.

The parent proves the *weighted* results

    weighted_amgm_le        : ∏ zᵢ^{wᵢ} ≤ ∑ wᵢ zᵢ
    weighted_amgm_eq_iff    : ∏ zᵢ^{wᵢ} = ∑ wᵢ zᵢ  ↔  all zᵢ equal
    weighted_amgm_lt_of_ne  : some zⱼ ≠ zₖ  →  ∏ zᵢ^{wᵢ} < ∑ wᵢ zᵢ

Specializing to the **uniform weights** `wᵢ = 1/n` (where `n = s.card`) collapses the
weighted geometric mean `∏ zᵢ^{1/n}` to the ordinary `n`-th root `(∏ zᵢ)^{1/n}` (via
`Real.finset_prod_rpow`) and the weighted arithmetic mean `∑ (1/n) zᵢ` to the ordinary
average `(∑ zᵢ)/n`. This turns the three weighted statements into their familiar
unweighted forms — in particular the equality case

    (∏ zᵢ)^{1/n} = (∑ zᵢ)/n   ↔   all zᵢ are equal,

which is the unweighted `n`-variable generalization of the parent's two-variable
`√(ab) = (a+b)/2 ↔ a = b`. The forward specialization requires only that `s` be
nonempty (so that `n ≥ 1` and the uniform weights sum to `1`).

## Main results

* `amgm_n_le` — the unweighted `n`-variable AM–GM inequality `(∏ zᵢ)^{1/n} ≤ (∑ zᵢ)/n`.
* `amgm_n_eq_iff` — equality `(∏ zᵢ)^{1/n} = (∑ zᵢ)/n` holds **iff all `zᵢ` are equal**.
* `amgm_n_lt_of_ne` — if some two of the (positive) values differ, the inequality is strict.

All exponents are real (`Real.rpow`). All results are fully machine-checked:
0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib
import Proofs.JensenInequalityOQ01

open Finset Real

variable {ι : Type*} {s : Finset ι} {z : ι → ℝ}

/-! ## Uniform-weight bridge

Each result below instantiates the parent's weighted theorem at the constant weight
`fun _ => (s.card : ℝ)⁻¹`. The two structural facts we need repeatedly are that these
weights are (strictly) positive and that they sum to `1`. -/

/-- **Unweighted `n`-variable AM–GM inequality.** For a nonempty finite index set `s` and
nonnegative data `z`, the `n`-th root of the product is at most the average, where
`n = s.card`. This is `weighted_amgm_le` at the uniform weights `1/n`. -/
theorem amgm_n_le (hs : s.Nonempty) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹) ≤ (∑ i ∈ s, z i) / (s.card : ℝ) := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hw : ∀ i ∈ s, (0 : ℝ) ≤ (s.card : ℝ)⁻¹ := fun _ _ => (inv_pos.mpr hcard).le
  have hw' : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hcard)]
  have h := weighted_amgm_le (w := fun _ => (s.card : ℝ)⁻¹) hw hw' hz
  simp only [] at h
  rwa [Real.finset_prod_rpow s z hz, ← Finset.mul_sum, ← div_eq_inv_mul] at h

/-- **Unweighted `n`-variable AM–GM equality case.** For a nonempty finite index set `s`
and nonnegative data `z`, the `n`-th root of the product equals the average **iff all the
data are equal** (`n = s.card`). This is the unweighted generalization of the parent's
two-variable `amgm_two_eq_iff`, obtained from `weighted_amgm_eq_iff` at uniform weights
`1/n`. -/
theorem amgm_n_eq_iff (hs : s.Nonempty) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹) = (∑ i ∈ s, z i) / (s.card : ℝ)
      ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hw : ∀ i ∈ s, (0 : ℝ) < (s.card : ℝ)⁻¹ := fun _ _ => inv_pos.mpr hcard
  have hw' : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hcard)]
  have h := weighted_amgm_eq_iff (w := fun _ => (s.card : ℝ)⁻¹) hw hw' hz
  simp only [] at h
  rwa [Real.finset_prod_rpow s z hz, ← Finset.mul_sum, ← div_eq_inv_mul] at h

/-- **Strict unweighted `n`-variable AM–GM.** For a nonempty finite index set `s` and
*strictly positive* data `z`, if some two of the values differ then the `n`-th root of the
product is *strictly* less than the average. This is `weighted_amgm_lt_of_ne` at uniform
weights `1/n`. -/
theorem amgm_n_lt_of_ne (hs : s.Nonempty) (hz : ∀ i ∈ s, 0 < z i)
    (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹) < (∑ i ∈ s, z i) / (s.card : ℝ) := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hw : ∀ i ∈ s, (0 : ℝ) < (s.card : ℝ)⁻¹ := fun _ _ => inv_pos.mpr hcard
  have hw' : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hcard)]
  have h := weighted_amgm_lt_of_ne (w := fun _ => (s.card : ℝ)⁻¹) hw hw' hz hne
  simp only [] at h
  rwa [Real.finset_prod_rpow s z (fun i hi => (hz i hi).le), ← Finset.mul_sum,
    ← div_eq_inv_mul] at h
