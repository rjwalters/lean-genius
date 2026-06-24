import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Lagrange's Identity — the Exact Cauchy–Schwarz Defect (cauchy-schwarz-oq-05)

## What This Proves

For finite real sequences `a, b` indexed by a `Finset` over a linearly ordered type,
Lagrange's identity gives the *exact* gap in the Cauchy–Schwarz inequality as a sum of
squared `2 × 2` minors over strictly ordered index pairs:

  (∑ aᵢ²)(∑ bᵢ²) − (∑ aᵢbᵢ)² = ∑_{i<j} (aᵢbⱼ − aⱼbᵢ)².

Because the right-hand side is a sum of squares it is `≥ 0`, which makes the Cauchy–Schwarz
inequality an immediate corollary, and it is `= 0` exactly when every minor `aᵢbⱼ − aⱼbᵢ`
vanishes — the proportionality / equality characterization.

This is the discrete shadow of `‖u‖²‖v‖² − ⟨u,v⟩² = ‖u ∧ v‖²`.

## Relation to the Parent

`CauchySchwarzOQ03.lean` records the **symmetric, doubled** form
`∑ᵢ∑ⱼ (aᵢbⱼ − aⱼbᵢ)² = 2·defect` (a full double sum, with a factor of 2). The result here is
the canonical **strict-upper-triangle** form: the defect equals the sum over `i < j` only, with
no factor of 2, exhibiting it directly as a sum over the distinct `2 × 2` minors. The bridge is a
general triangle-doubling lemma (`sum_offDiag_eq_two_mul_sum_filter_lt`) for symmetric kernels.

## Status
- [x] Triangle-doubling lemma for symmetric kernels
- [x] Lagrange's identity (strict-upper-triangle form)
- [x] Cauchy–Schwarz inequality as a corollary
- [x] Equality characterization via vanishing minors

Verified, 0-axiom (`propext` / `Classical.choice` / `Quot.sound` only).
-/

open Finset

namespace LagrangeIdentityCS

variable {ι : Type*} [LinearOrder ι]

/-- **Triangle-doubling for a symmetric kernel.**
Summing a symmetric function `F` over all *distinct* ordered pairs of `s` (the off-diagonal)
counts each unordered pair twice, so it equals twice the sum over strictly increasing pairs. -/
theorem sum_offDiag_eq_two_mul_sum_filter_lt (s : Finset ι) (F : ι → ι → ℝ)
    (hsymm : ∀ i j, F i j = F j i) :
    ∑ p ∈ s.offDiag, F p.1 p.2
      = 2 * ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), F p.1 p.2 := by
  rw [← Finset.sum_filter_add_sum_filter_not s.offDiag (fun p => p.1 < p.2), two_mul]
  congr 1
  -- The `¬ (i < j)` part of the off-diagonal is the strictly-decreasing part, which the
  -- swap `(i, j) ↦ (j, i)` carries bijectively onto the strictly-increasing part.
  refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [mem_filter, mem_offDiag] at hp ⊢
    obtain ⟨⟨hi, hj, hij⟩, hlt⟩ := hp
    exact ⟨⟨hj, hi, fun h => hij h.symm⟩, lt_of_le_of_ne (not_lt.1 hlt) hij.symm⟩
  · rintro ⟨i, j⟩ hp
    simp only [mem_filter, mem_offDiag] at hp ⊢
    obtain ⟨⟨hi, hj, hij⟩, hlt⟩ := hp
    exact ⟨⟨hj, hi, fun h => hij h.symm⟩, not_lt.2 hlt.le⟩
  · rintro ⟨i, j⟩ _; rfl
  · rintro ⟨i, j⟩ _; rfl
  · rintro ⟨i, j⟩ _; exact hsymm i j

/-- **Lagrange's identity.** The Cauchy–Schwarz defect equals the sum of squared `2 × 2`
minors over strictly increasing index pairs. -/
theorem lagrange_identity (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) - (∑ i ∈ s, a i * b i) ^ 2
      = ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
          (a p.1 * b p.2 - a p.2 * b p.1) ^ 2 := by
  set F : ι → ι → ℝ := fun i j => (a i * b j - a j * b i) ^ 2 with hF
  -- The symmetric double sum equals twice the defect (the "doubled" Lagrange identity).
  have hdouble : ∑ i ∈ s, ∑ j ∈ s, F i j
      = 2 * ((∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) - (∑ i ∈ s, a i * b i) ^ 2) := by
    simp only [hF, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have ha : ∑ i ∈ s, ∑ j ∈ s, (a i * b j) ^ 2 =
        (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) := by
      simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
    have hc : ∑ i ∈ s, ∑ j ∈ s, (a j * b i) ^ 2 =
        (∑ j ∈ s, a j ^ 2) * (∑ i ∈ s, b i ^ 2) := by
      rw [Finset.sum_comm]; simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
    have hb : ∑ i ∈ s, ∑ j ∈ s, 2 * (a i * b j) * (a j * b i) =
        2 * (∑ i ∈ s, a i * b i) ^ 2 := by
      simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
      congr 1; ext i; congr 1; ext j; ring
    rw [ha, hc, hb]; ring
  -- The same double sum, split into diagonal (zero) + off-diagonal (doubled upper triangle).
  have hsplit : ∑ i ∈ s, ∑ j ∈ s, F i j
      = 2 * ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), F p.1 p.2 := by
    have hprod : ∑ i ∈ s, ∑ j ∈ s, F i j = ∑ p ∈ s ×ˢ s, F p.1 p.2 := by
      rw [Finset.sum_product']
    rw [hprod, ← diag_union_offDiag s, Finset.sum_union (disjoint_diag_offDiag s),
        Finset.sum_diag]
    have hdiag : ∑ i ∈ s, F i i = 0 := by
      simp only [hF]; apply Finset.sum_eq_zero; intro i _; ring
    rw [hdiag, zero_add,
        sum_offDiag_eq_two_mul_sum_filter_lt s F (fun i j => by simp only [hF]; ring)]
  have hupper : 2 * ((∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) - (∑ i ∈ s, a i * b i) ^ 2)
      = 2 * ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), F p.1 p.2 := by
    rw [← hdouble, hsplit]
  have := mul_left_cancel₀ (two_ne_zero) hupper
  simpa only [hF] using this

/-- **Cauchy–Schwarz inequality** as an immediate corollary: the defect is a sum of squares,
hence non-negative. -/
theorem cauchy_schwarz (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
  have h := lagrange_identity s a b
  have hnn : 0 ≤ ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
      (a p.1 * b p.2 - a p.2 * b p.1) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- **Equality characterization.** Cauchy–Schwarz holds with equality iff every `2 × 2`
minor over a strictly increasing pair vanishes (the proportionality condition). -/
theorem cauchy_schwarz_eq_iff (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i * b i) ^ 2 = (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2)
      ↔ ∀ p ∈ s.offDiag.filter (fun p => p.1 < p.2), a p.1 * b p.2 - a p.2 * b p.1 = 0 := by
  have h := lagrange_identity s a b
  rw [eq_comm, ← sub_eq_zero, h,
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  exact forall_congr' fun p => imp_congr_right fun _ => pow_eq_zero_iff (by norm_num)

end LagrangeIdentityCS
