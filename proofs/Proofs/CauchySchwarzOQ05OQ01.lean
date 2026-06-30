import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Weighted Lagrange Identity — the Exact Weighted Cauchy–Schwarz Defect (cauchy-schwarz-oq-05-oq-01)

## What This Proves

For finite real sequences `a, b` and an arbitrary weight sequence `w` indexed by a `Finset`
over a linearly ordered type, the **weighted Lagrange identity** gives the *exact* gap in the
weighted Cauchy–Schwarz inequality as a weighted sum of squared `2 × 2` minors over strictly
ordered index pairs:

  (∑ wᵢaᵢ²)(∑ wᵢbᵢ²) − (∑ wᵢaᵢbᵢ)² = ∑_{i<j} wᵢwⱼ(aᵢbⱼ − aⱼbᵢ)².

The identity itself is a **purely algebraic** statement: it holds for *any* real weights `w`,
with no sign restriction (it is a polynomial identity in `a`, `b`, `w`). Non-negativity of the
weights enters only for the inequality corollary: when each `wᵢ ≥ 0`, every term on the right is
a product of non-negative factors, so the defect is `≥ 0` and the weighted Cauchy–Schwarz
inequality follows; equality holds exactly when every weighted minor vanishes.

## Relation to the Parent

`CauchySchwarzOQ05.lean` proves the **unweighted** Lagrange identity
`(∑ aᵢ²)(∑ bᵢ²) − (∑ aᵢbᵢ)² = ∑_{i<j} (aᵢbⱼ − aⱼbᵢ)²`. The result here carries an arbitrary
weight `wᵢ` through the entire computation, recovering the parent verbatim at `w ≡ 1`. The key
new content is the pointwise factorisation of the *weighted* symmetric kernel

  wᵢwⱼ(aᵢbⱼ − aⱼbᵢ)² = (wᵢaᵢ²)(wⱼbⱼ²) + (wᵢbᵢ²)(wⱼaⱼ²) − 2(wᵢaᵢbᵢ)(wⱼaⱼbⱼ),

which makes the double sum collapse to `2·(weighted defect)` via `Finset.sum_mul_sum`. The
triangle-doubling lemma for symmetric kernels is shared with the parent.

## Status
- [x] Triangle-doubling lemma for symmetric kernels
- [x] Weighted Lagrange identity (strict-upper-triangle form)
- [x] Weighted Cauchy–Schwarz inequality as a corollary (`wᵢ ≥ 0`)
- [x] Equality characterization via vanishing weighted minors

Verified, 0-axiom (`propext` / `Classical.choice` / `Quot.sound` only).
-/

open Finset

namespace WeightedLagrangeCS

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

/-- **Weighted Lagrange identity.** The weighted Cauchy–Schwarz defect equals the weighted sum
of squared `2 × 2` minors over strictly increasing index pairs. Holds for *arbitrary* real
weights `w` — it is a polynomial identity, no sign hypothesis is needed. -/
theorem weighted_lagrange_identity (s : Finset ι) (w a b : ι → ℝ) :
    (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2)
        - (∑ i ∈ s, w i * (a i * b i)) ^ 2
      = ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
          w p.1 * w p.2 * (a p.1 * b p.2 - a p.2 * b p.1) ^ 2 := by
  set F : ι → ι → ℝ := fun i j => w i * w j * (a i * b j - a j * b i) ^ 2 with hF
  -- The symmetric double sum equals twice the weighted defect.
  have hdouble : ∑ i ∈ s, ∑ j ∈ s, F i j
      = 2 * ((∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2)
              - (∑ i ∈ s, w i * (a i * b i)) ^ 2) := by
    -- Pointwise factorisation of the weighted kernel into a sum of rank-one products.
    have hrw : ∑ i ∈ s, ∑ j ∈ s, F i j
        = ∑ i ∈ s, ∑ j ∈ s,
            ((w i * a i ^ 2) * (w j * b j ^ 2)
              + (w i * b i ^ 2) * (w j * a j ^ 2)
              - 2 * (w i * (a i * b i)) * (w j * (a j * b j))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [hF]; ring
    rw [hrw]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have ha : ∑ i ∈ s, ∑ j ∈ s, (w i * a i ^ 2) * (w j * b j ^ 2)
        = (∑ i ∈ s, w i * a i ^ 2) * (∑ j ∈ s, w j * b j ^ 2) :=
      (Finset.sum_mul_sum s s _ _).symm
    have hc : ∑ i ∈ s, ∑ j ∈ s, (w i * b i ^ 2) * (w j * a j ^ 2)
        = (∑ i ∈ s, w i * b i ^ 2) * (∑ j ∈ s, w j * a j ^ 2) :=
      (Finset.sum_mul_sum s s _ _).symm
    have hb : ∑ i ∈ s, ∑ j ∈ s, 2 * (w i * (a i * b i)) * (w j * (a j * b j))
        = 2 * (∑ i ∈ s, w i * (a i * b i)) ^ 2 := by
      have h2 : ∑ i ∈ s, ∑ j ∈ s, 2 * (w i * (a i * b i)) * (w j * (a j * b j))
          = 2 * ∑ i ∈ s, ∑ j ∈ s, (w i * (a i * b i)) * (w j * (a j * b j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [h2, ← Finset.sum_mul_sum]; ring
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
  have hupper : 2 * ((∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2)
              - (∑ i ∈ s, w i * (a i * b i)) ^ 2)
      = 2 * ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), F p.1 p.2 := by
    rw [← hdouble, hsplit]
  have := mul_left_cancel₀ (two_ne_zero) hupper
  simpa only [hF] using this

/-- **Weighted Cauchy–Schwarz inequality** as an immediate corollary: with non-negative
weights the defect is a sum of non-negative terms, hence `≥ 0`. -/
theorem weighted_cauchy_schwarz (s : Finset ι) (w a b : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (a i * b i)) ^ 2
      ≤ (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) := by
  have h := weighted_lagrange_identity s w a b
  have hnn : 0 ≤ ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
      w p.1 * w p.2 * (a p.1 * b p.2 - a p.2 * b p.1) ^ 2 := by
    refine Finset.sum_nonneg fun p hp => ?_
    simp only [mem_filter, mem_offDiag] at hp
    obtain ⟨⟨hp1, hp2, _⟩, _⟩ := hp
    exact mul_nonneg (mul_nonneg (hw p.1 hp1) (hw p.2 hp2)) (sq_nonneg _)
  linarith

/-- **Equality characterization.** With non-negative weights, weighted Cauchy–Schwarz holds with
equality iff every weighted `2 × 2` minor over a strictly increasing pair vanishes. -/
theorem weighted_cauchy_schwarz_eq_iff (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (a i * b i)) ^ 2
        = (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2)
      ↔ ∀ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
          w p.1 * w p.2 * (a p.1 * b p.2 - a p.2 * b p.1) ^ 2 = 0 := by
  have h := weighted_lagrange_identity s w a b
  have hnn : ∀ p ∈ s.offDiag.filter (fun p => p.1 < p.2),
      0 ≤ w p.1 * w p.2 * (a p.1 * b p.2 - a p.2 * b p.1) ^ 2 := by
    intro p hp
    simp only [mem_filter, mem_offDiag] at hp
    obtain ⟨⟨hp1, hp2, _⟩, _⟩ := hp
    exact mul_nonneg (mul_nonneg (hw p.1 hp1) (hw p.2 hp2)) (sq_nonneg _)
  rw [eq_comm, ← sub_eq_zero, h, Finset.sum_eq_zero_iff_of_nonneg hnn]

end WeightedLagrangeCS
