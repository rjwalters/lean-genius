import Mathlib

/-
# Weighted Chebyshev sum inequality from a monovariance hypothesis

The Mathlib Chebyshev file (`Mathlib/Algebra/Order/Chebyshev.lean`) proves the
*unweighted* sum inequality

  (∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ #s * ∑ i ∈ s, f i * g i

for `MonovaryOn f g s` (equivalently, similarly sorted sequences), and the reverse
inequality for `AntivaryOn`. It has **no** weighted analogue.

This file fills that gap. Given nonnegative weights `w : ι → ℝ` with total mass
`W = ∑ i ∈ s, w i`, and `f`, `g` monovarying on `s`, we prove the
**weighted Chebyshev sum inequality**

  (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i) ≤ W * ∑ i ∈ s, w i * f i * g i,

and the reverse for antivarying `f`, `g`. Taking `w ≡ 1` recovers the Mathlib `#s`
form, so this is a strict generalization.

The engine is the **weighted monovariance identity**

  2 (W·∑ wᵢfᵢgᵢ − (∑ wᵢfᵢ)(∑ wᵢgᵢ))
    = ∑ᵢ ∑ⱼ wᵢ wⱼ (fᵢ − fⱼ)(gᵢ − gⱼ),

whose right-hand side is a sum of products of nonnegative factors (each
`(fᵢ − fⱼ)(gᵢ − gⱼ) ≥ 0` because `f` and `g` monovary), hence `≥ 0`.

All results are fully verified with no extra axioms.
-/

namespace ChebyshevSumWeighted

open Finset

variable {ι : Type*} {s : Finset ι} {w f g : ι → ℝ}

/-! ## The sign lemmas for monovarying / antivarying pairs -/

/-- If `f` and `g` monovary on `s`, then for any two indices `i, j ∈ s` the cross
difference `(f i - f j) * (g i - g j)` is nonnegative: the two factors always carry the
same sign. -/
theorem sub_mul_sub_nonneg_of_monovaryOn (hfg : MonovaryOn f g s) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) : 0 ≤ (f i - f j) * (g i - g j) := by
  rcases lt_trichotomy (g i) (g j) with h | h | h
  · -- `g i < g j` forces `f i ≤ f j`: both factors are `≤ 0`.
    have hf : f i ≤ f j := hfg hi hj h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ f j - f i)
      (by linarith : (0 : ℝ) ≤ g j - g i)]
  · -- equal `g`-values kill the second factor.
    have : g i - g j = 0 := by linarith
    rw [this, mul_zero]
  · -- `g j < g i` forces `f j ≤ f i`: both factors are `≥ 0`.
    have hf : f j ≤ f i := hfg hj hi h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ f i - f j)
      (by linarith : (0 : ℝ) ≤ g i - g j)]

/-- If `f` and `g` antivary on `s`, then `(f i - f j) * (g i - g j) ≤ 0` for all
`i, j ∈ s`: the two factors always carry opposite signs. -/
theorem sub_mul_sub_nonpos_of_antivaryOn (hfg : AntivaryOn f g s) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) : (f i - f j) * (g i - g j) ≤ 0 := by
  rcases lt_trichotomy (g i) (g j) with h | h | h
  · -- `g i < g j` forces `f j ≤ f i`: first factor `≥ 0`, second `≤ 0`.
    have hf : f j ≤ f i := hfg hi hj h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ f i - f j)
      (by linarith : (0 : ℝ) ≤ g j - g i)]
  · have : g i - g j = 0 := by linarith
    rw [this, mul_zero]
  · -- `g j < g i` forces `f i ≤ f j`: first factor `≤ 0`, second `≥ 0`.
    have hf : f i ≤ f j := hfg hj hi h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ f j - f i)
      (by linarith : (0 : ℝ) ≤ g i - g j)]

/-! ## The weighted monovariance identity -/

/-- **Weighted monovariance identity.** The symmetric double sum of
`wᵢ wⱼ (fᵢ − fⱼ)(gᵢ − gⱼ)` equals twice the Chebyshev defect
`W·∑ wᵢfᵢgᵢ − (∑ wᵢfᵢ)(∑ wᵢgᵢ)`. This holds for arbitrary real data — no sign or
monotonicity hypothesis is needed. -/
theorem two_mul_chebyshev_defect_eq (w f g : ι → ℝ) (s : Finset ι) :
    ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j))
      = 2 * ((∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i)
        - 2 * ((∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i) := by
  -- The four "monomial" double sums, each collapsing to a product of two single sums.
  have h1 : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i * g i)
      = (∑ i ∈ s, w i * f i * g i) * ∑ j ∈ s, w j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (f j * g j)
      = (∑ i ∈ s, w i) * ∑ j ∈ s, w j * f j * g j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i * g j)
      = (∑ i ∈ s, w i * f i) * ∑ j ∈ s, w j * g j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h4 : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (f j * g i)
      = (∑ i ∈ s, w i * g i) * ∑ j ∈ s, w j * f j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- Expand the summand and split the double sum into the four monomial pieces.
  have hsplit : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j))
      = (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i * g i))
        - (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i * g j))
        - (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f j * g i))
        + (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f j * g j)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, h1, h2, h3, h4]
  ring

/-! ## Weighted Chebyshev inequalities -/

/-- **Weighted Chebyshev sum inequality** (similarly sorted data). For nonnegative
weights `w` and functions `f`, `g` that monovary on `s`, the product of the weighted
sums is at most the total weight times the weighted sum of products. With `w ≡ 1` this
is the Mathlib lemma `MonovaryOn.sum_mul_sum_le_card_mul_sum`. -/
theorem weighted_sum_mul_sum_le (hfg : MonovaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i := by
  have hD : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) := by
    refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
    have := sub_mul_sub_nonneg_of_monovaryOn hfg hi hj
    have hwi := hw i hi
    have hwj := hw j hj
    positivity
  rw [two_mul_chebyshev_defect_eq] at hD
  linarith

/-- **Reverse weighted Chebyshev sum inequality** (oppositely sorted data). For
nonnegative weights and `f`, `g` antivarying on `s`, the inequality reverses. With
`w ≡ 1` this is `AntivaryOn.card_mul_sum_le_sum_mul_sum`. -/
theorem weighted_antivary_le_sum_mul_sum (hfg : AntivaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i
      ≤ (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i := by
  have hD : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) ≤ 0 := by
    refine Finset.sum_nonpos fun i hi => Finset.sum_nonpos fun j hj => ?_
    have hsign := sub_mul_sub_nonpos_of_antivaryOn hfg hi hj
    have hwi := hw i hi
    have hwj := hw j hj
    have : 0 ≤ w i * w j := mul_nonneg hwi hwj
    nlinarith [mul_nonneg this (neg_nonneg.mpr hsign)]
  rw [two_mul_chebyshev_defect_eq] at hD
  linarith

/-! ## Monotone-sequence corollaries -/

variable [LinearOrder ι]

/-- **Weighted Chebyshev for monotone data.** If `f` and `g` are monotone on `s`, they
monovary there, so the weighted Chebyshev inequality applies. This is the form named in
the open question: a weighted inequality for similarly sorted (monotone) sequences. -/
theorem weighted_chebyshev_monotoneOn (hf : MonotoneOn f s) (hg : MonotoneOn g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i :=
  weighted_sum_mul_sum_le (hf.monovaryOn hg) hw

/-- **Reverse weighted Chebyshev for oppositely monotone data.** If `f` is monotone and
`g` is antitone on `s`, the weighted inequality reverses. -/
theorem weighted_chebyshev_antitoneOn (hf : MonotoneOn f s) (hg : AntitoneOn g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i
      ≤ (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i :=
  weighted_antivary_le_sum_mul_sum (hf.antivaryOn hg) hw

/-! ## Weighted Cauchy–Schwarz corollary and unweighted recovery -/

omit [LinearOrder ι] in
/-- **Weighted Cauchy–Schwarz-type corollary.** The self-monovarying case `f = g` gives
`(∑ wᵢfᵢ)² ≤ (∑ wᵢ)(∑ wᵢfᵢ²)`, a weighted power-mean / Cauchy–Schwarz bound, valid for
*any* `f` (every function monovaries with itself). -/
theorem weighted_sq_sum_le (w f : ι → ℝ) (s : Finset ι) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i ^ 2 := by
  have h := weighted_sum_mul_sum_le (w := w) (monovaryOn_self f s) hw
  rw [sq]
  calc (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * f i
      ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * f i := h
    _ = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i ^ 2 := by
          refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_); ring

omit [LinearOrder ι] in
/-- Sanity check: with all weights equal to `1`, the weighted inequality collapses to the
classical Mathlib `#s` form `(∑ f)(∑ g) ≤ #s · ∑ f g`. -/
theorem unweighted_recovery (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ (#s : ℝ) * ∑ i ∈ s, f i * g i := by
  have h := weighted_sum_mul_sum_le (w := fun _ => (1 : ℝ)) hfg (fun i _ => by norm_num)
  simpa using h

/-! ## Worked instance -/

/-- A concrete weighted instance with weights `1, 2, 3` on the increasing sequence
`0, 1, 2` (against itself), obtained from `weighted_sq_sum_le`. It evaluates to
`(1·0 + 2·1 + 3·2)² = 64 ≤ 6 · (1·0² + 2·1² + 3·2²) = 6·14 = 84`. -/
example :
    (∑ i ∈ range 3, ((i : ℝ) + 1) * (i : ℝ)) ^ 2
      ≤ (∑ i ∈ range 3, ((i : ℝ) + 1)) * ∑ i ∈ range 3, ((i : ℝ) + 1) * (i : ℝ) ^ 2 :=
  weighted_sq_sum_le (fun i : ℕ => (i : ℝ) + 1) (fun i : ℕ => (i : ℝ)) (range 3)
    fun i _ => by positivity

/-- The instance above, with the sums evaluated: `64 ≤ 84`. -/
example : ((0 : ℝ) + 2 * 1 + 3 * 2) ^ 2 ≤ (1 + 2 + 3) * (0 + 2 * 1 ^ 2 + 3 * 2 ^ 2) := by
  norm_num

end ChebyshevSumWeighted
