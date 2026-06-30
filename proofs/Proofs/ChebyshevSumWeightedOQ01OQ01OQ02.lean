import Mathlib

/-
# Strict Weighted Chebyshev Sum Inequality and its Equality Case

The parent entry `ChebyshevSumWeightedOQ01OQ01` proves the (non-strict) weighted
Chebyshev sum inequality

  (∑ᵢ wᵢfᵢ)(∑ᵢ wᵢgᵢ)  ≤  (∑ᵢ wᵢ)(∑ᵢ wᵢfᵢgᵢ)

for nonnegative weights `w` and similarly sorted (`MonovaryOn`) data `f`, `g`.
Its engine is the **weighted monovariance identity**

  ∑ᵢ ∑ⱼ wᵢwⱼ(fᵢ − fⱼ)(gᵢ − gⱼ)
    = 2[(∑ᵢ wᵢ)(∑ᵢ wᵢfᵢgᵢ) − (∑ᵢ wᵢfᵢ)(∑ᵢ wᵢgᵢ)],

which writes the **Chebyshev defect** `D = (∑wᵢ)(∑wᵢfᵢgᵢ) − (∑wᵢfᵢ)(∑wᵢgᵢ)` as
*half a sum of nonnegative cross terms* `wᵢwⱼ(fᵢ − fⱼ)(gᵢ − gⱼ) ≥ 0`.

That representation does more than prove `D ≥ 0`; it pins down exactly *when the
inequality is tight* and *when it is strict*:

* **Equality** holds iff **every** cross term vanishes
  (`weighted_chebyshev_eq_iff`).  A sum of nonnegative reals is zero iff each
  summand is zero (`Finset.sum_eq_zero_iff_of_nonneg`).  With strictly positive
  weights this simplifies to: there is no pair `i, j ∈ s` on which `f` and `g`
  *both* strictly vary (`weighted_chebyshev_eq_iff_of_pos`).  In particular the
  inequality degenerates to equality whenever `f` or `g` is constant on `s`.

* **Strictness** holds as soon as a *single* positively weighted pair has a
  strictly positive cross term (`weighted_chebyshev_strict`), e.g. two indices
  `a, b ∈ s` with `wₐ, w_b > 0` at which `f` and `g` both genuinely differ
  (`weighted_chebyshev_strict_of_ne`).  This uses `Finset.sum_pos'`: a sum of
  nonnegative reals is positive once one summand is.

Neither the equality characterisation nor the strict inequality is in Mathlib
(whose Chebyshev file `Mathlib/Algebra/Order/Chebyshev.lean` records only the
non-strict unweighted bound).  All results are over `ℝ`, fully verified, no
`sorry`, no extra axioms.
-/

namespace ChebyshevSumWeightedStrict

open Finset

-- The algebraic identity needs no order structure; the sign and order facts use ℝ.
set_option linter.unusedSectionVars false

variable {ι : Type*} {s : Finset ι} {w f g : ι → ℝ}

/-! ## Sign lemmas for monovarying pairs -/

/-- If `f` and `g` monovary on `s`, the cross product `(fᵢ − fⱼ)(gᵢ − gⱼ)` is
nonnegative for all `i, j ∈ s`: the two factors carry the same sign. -/
theorem sub_mul_sub_nonneg_of_monovaryOn (hfg : MonovaryOn f g s) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) : 0 ≤ (f i - f j) * (g i - g j) := by
  rcases lt_trichotomy (g i) (g j) with h | h | h
  · have hf : f i ≤ f j := hfg hi hj h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ f j - f i)
      (by linarith : (0 : ℝ) ≤ g j - g i)]
  · have : g i - g j = 0 := by linarith
    rw [this, mul_zero]
  · have hf : f j ≤ f i := hfg hj hi h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ f i - f j)
      (by linarith : (0 : ℝ) ≤ g i - g j)]

/-- If `f` and `g` monovary on `s` and **both** genuinely differ at `i, j ∈ s`
(`f i ≠ f j` and `g i ≠ g j`), the cross product is *strictly* positive. -/
theorem sub_mul_sub_pos_of_monovaryOn (hfg : MonovaryOn f g s) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hf : f i ≠ f j) (hg : g i ≠ g j) :
    0 < (f i - f j) * (g i - g j) := by
  rcases lt_trichotomy (g i) (g j) with h | h | h
  · have hfle : f i ≤ f j := hfg hi hj h
    have hflt : f i < f j := lt_of_le_of_ne hfle hf
    nlinarith [mul_pos (by linarith : (0 : ℝ) < f j - f i)
      (by linarith : (0 : ℝ) < g j - g i)]
  · exact absurd h hg
  · have hfle : f j ≤ f i := hfg hj hi h
    have hflt : f j < f i := lt_of_le_of_ne hfle (Ne.symm hf)
    nlinarith [mul_pos (by linarith : (0 : ℝ) < f i - f j)
      (by linarith : (0 : ℝ) < g i - g j)]

/-- Each weighted cross term is nonnegative (nonnegative weights, monovariance). -/
theorem term_nonneg (hfg : MonovaryOn f g s) (hw : ∀ i ∈ s, 0 ≤ w i) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) : 0 ≤ w i * w j * ((f i - f j) * (g i - g j)) := by
  have h := sub_mul_sub_nonneg_of_monovaryOn hfg hi hj
  have hwi := hw i hi
  have hwj := hw j hj
  positivity

/-! ## The weighted monovariance identity (defect = ½ the double sum) -/

/-- **Weighted monovariance identity.** The symmetric double sum of
`wᵢwⱼ(fᵢ − fⱼ)(gᵢ − gⱼ)` equals twice the Chebyshev defect. Holds for arbitrary
real data — no sign or monotonicity hypothesis. -/
theorem two_mul_chebyshev_defect_eq (w f g : ι → ℝ) (s : Finset ι) :
    ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j))
      = 2 * ((∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i)
        - 2 * ((∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i) := by
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

/-! ## The non-strict inequality (recalled, self-contained) -/

/-- **Weighted Chebyshev sum inequality.** For nonnegative weights and monovarying
`f`, `g`, the product of the weighted sums is at most total weight times the
weighted sum of products. -/
theorem weighted_sum_mul_sum_le (hfg : MonovaryOn f g s) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i := by
  have hD : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => term_nonneg hfg hw hi hj
  rw [two_mul_chebyshev_defect_eq] at hD
  linarith

/-! ## The equality case -/

/-- **Equality case.** Under monovariance with nonnegative weights, the weighted
Chebyshev inequality is an *equality* iff every weighted cross term vanishes. -/
theorem weighted_chebyshev_eq_iff (hfg : MonovaryOn f g s) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
        = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i
      ↔ ∀ i ∈ s, ∀ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) = 0 := by
  have key : (∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j))) = 0
      ↔ ∀ i ∈ s, ∀ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => Finset.sum_nonneg fun j hj => term_nonneg hfg hw hi hj)]
    apply forall_congr'; intro i
    apply imp_congr_right; intro hi
    exact Finset.sum_eq_zero_iff_of_nonneg fun j hj => term_nonneg hfg hw hi hj
  rw [← key, two_mul_chebyshev_defect_eq]
  constructor <;> intro h <;> linarith

/-- **Equality case, strictly positive weights.** When all weights are positive,
equality holds iff there is no pair `i, j ∈ s` on which `f` and `g` both strictly
vary: `(fᵢ − fⱼ)(gᵢ − gⱼ) = 0` for all `i, j ∈ s`. -/
theorem weighted_chebyshev_eq_iff_of_pos (hfg : MonovaryOn f g s) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
        = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i
      ↔ ∀ i ∈ s, ∀ j ∈ s, (f i - f j) * (g i - g j) = 0 := by
  rw [weighted_chebyshev_eq_iff hfg (fun i hi => (hw i hi).le)]
  apply forall_congr'; intro i; apply imp_congr_right; intro hi
  apply forall_congr'; intro j; apply imp_congr_right; intro hj
  constructor
  · intro h
    have hwij : w i * w j ≠ 0 := ne_of_gt (mul_pos (hw i hi) (hw j hj))
    exact (mul_eq_zero.mp h).resolve_left hwij
  · intro h; rw [h, mul_zero]

/-- **Equality case, human-readable form.** With strictly positive weights, the
weighted Chebyshev inequality is an *equality* iff `f` is constant on `s` **or**
`g` is constant on `s`. This is the form recorded in the parent's open question:
the termwise condition `(fᵢ − fⱼ)(gᵢ − gⱼ) = 0` for all `i, j ∈ s` is, under
monovariance, equivalent to one of the two sequences being constant. -/
theorem weighted_chebyshev_eq_iff_const (hfg : MonovaryOn f g s) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
        = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i
      ↔ (∀ i ∈ s, ∀ j ∈ s, f i = f j) ∨ (∀ i ∈ s, ∀ j ∈ s, g i = g j) := by
  rw [weighted_chebyshev_eq_iff_of_pos hfg hw]
  constructor
  · intro H
    -- From a vanishing cross product: distinct `f` forces equal `g`, and vice versa.
    have hFG : ∀ p ∈ s, ∀ q ∈ s, f p ≠ f q → g p = g q := fun p hp q hq hpq => by
      rcases mul_eq_zero.mp (H p hp q hq) with h | h
      · exact absurd (sub_eq_zero.mp h) hpq
      · exact sub_eq_zero.mp h
    have hGF : ∀ p ∈ s, ∀ q ∈ s, g p ≠ g q → f p = f q := fun p hp q hq hpq => by
      rcases mul_eq_zero.mp (H p hp q hq) with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (sub_eq_zero.mp h) hpq
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨a, ha, b, hb, hab⟩, ⟨c, hc, d, hd, hcd⟩⟩ := hcon
    have hgab : g a = g b := hFG a ha b hb hab
    by_cases hac : g a = g c
    · have had : g a ≠ g d := by rw [hac]; exact hcd
      have hfad : f a = f d := hGF a ha d hd had
      have hbd : g b ≠ g d := by rw [← hgab, hac]; exact hcd
      have hfbd : f b = f d := hGF b hb d hd hbd
      exact hab (hfad.trans hfbd.symm)
    · have hfac : f a = f c := hGF a ha c hc hac
      have hbc : g b ≠ g c := by rw [← hgab]; exact hac
      have hfbc : f b = f c := hGF b hb c hc hbc
      exact hab (hfac.trans hfbc.symm)
  · rintro (hf | hg) i hi j hj
    · rw [hf i hi j hj]; ring
    · rw [hg i hi j hj]; ring

/-- If `f` is constant on `s`, the inequality degenerates to equality. -/
theorem weighted_chebyshev_eq_of_const_left (hfg : MonovaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, ∀ j ∈ s, f i = f j) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i := by
  rw [weighted_chebyshev_eq_iff hfg hw]
  intro i hi j hj
  rw [hf i hi j hj]; ring

/-- If `g` is constant on `s`, the inequality degenerates to equality. -/
theorem weighted_chebyshev_eq_of_const_right (hfg : MonovaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hg : ∀ i ∈ s, ∀ j ∈ s, g i = g j) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i := by
  rw [weighted_chebyshev_eq_iff hfg hw]
  intro i hi j hj
  rw [hg i hi j hj]; ring

/-! ## The strict inequality -/

/-- **Strict weighted Chebyshev sum inequality.** If two positively weighted
indices `a, b ∈ s` have a strictly positive cross product, the inequality is
strict. -/
theorem weighted_chebyshev_strict (hfg : MonovaryOn f g s) (hw : ∀ i ∈ s, 0 ≤ w i)
    {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hwa : 0 < w a) (hwb : 0 < w b)
    (hab : 0 < (f a - f b) * (g a - g b)) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      < (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i := by
  have hDpos : 0 < ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) := by
    refine Finset.sum_pos'
      (fun i hi => Finset.sum_nonneg fun j hj => term_nonneg hfg hw hi hj) ⟨a, ha, ?_⟩
    refine Finset.sum_pos' (fun j hj => term_nonneg hfg hw ha hj) ⟨b, hb, ?_⟩
    exact mul_pos (mul_pos hwa hwb) hab
  rw [two_mul_chebyshev_defect_eq] at hDpos
  linarith

/-- **Strict inequality from a genuinely varying positively weighted pair.** If
`a, b ∈ s` have positive weights and `f`, `g` both differ there, the inequality is
strict. -/
theorem weighted_chebyshev_strict_of_ne (hfg : MonovaryOn f g s) (hw : ∀ i ∈ s, 0 ≤ w i)
    {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hwa : 0 < w a) (hwb : 0 < w b)
    (hf : f a ≠ f b) (hg : g a ≠ g b) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      < (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i :=
  weighted_chebyshev_strict hfg hw ha hb hwa hwb
    (sub_mul_sub_pos_of_monovaryOn hfg ha hb hf hg)

/-! ## Worked instances -/

/- Concrete **strict** instance: unit weights on `{0, 1, 2}` with `f = g = id`.
`(0+1+2)² = 9 < 3·(0²+1²+2²) = 3·5 = 15`, witnessed by the strict variation at
`a = 0`, `b = 1`. -/
set_option linter.unusedVariables false in
example :
    (∑ i ∈ range 3, (1 : ℝ) * (i : ℝ)) * (∑ i ∈ range 3, (1 : ℝ) * (i : ℝ))
      < (∑ i ∈ range 3, (1 : ℝ)) * ∑ i ∈ range 3, (1 : ℝ) * (i : ℝ) * (i : ℝ) := by
  exact weighted_chebyshev_strict_of_ne (w := fun _ => (1 : ℝ))
    (f := fun i => (i : ℝ)) (g := fun i => (i : ℝ)) (s := Finset.range 3)
    (monovaryOn_self _ _) (fun _ _ => by norm_num)
    (a := 0) (b := 1) (by decide) (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Concrete **equality** instance: with `f` constant the bound is tight. -/
example (w g : ι → ℝ) (s : Finset ι) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (5 : ℝ)) * (∑ i ∈ s, w i * g i)
      = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (5 : ℝ) * g i :=
  weighted_chebyshev_eq_of_const_left
    (f := fun _ => (5 : ℝ)) (fun _ _ _ _ _ => le_refl _) hw (fun _ _ _ _ => rfl)

end ChebyshevSumWeightedStrict
