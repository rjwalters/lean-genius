/-
# Weighted Chebyshev sum inequality and its equality case (weighted covariance identity)

The companion file `RearrangementChebyshevEqOQ01` proves the **unweighted** Chebyshev
sum inequality and its equality case from the discrete covariance identity
  `∑ᵢ∑ⱼ (fᵢ − fⱼ)(gᵢ − gⱼ) = 2·(#s·∑ fᵢgᵢ − (∑ fᵢ)(∑ gᵢ))`.

This file answers the natural follow-up: derive the **weighted** version with weights
`wᵢ ≥ 0` from the **weighted covariance identity**
  `∑ᵢ∑ⱼ wᵢwⱼ(fᵢ − fⱼ)(gᵢ − gⱼ)
      = 2·((∑ wᵢ)·(∑ wᵢfᵢgᵢ) − (∑ wᵢfᵢ)(∑ wᵢgᵢ))`,
valid for *any* real-valued `w, f, g` (no sign or order hypotheses). It is the finite,
unnormalised analogue of `2 · W² · Cov_w(f, g)` for the probability measure `wᵢ/W`.

From it, with zero extra axioms:
* `weighted_covariance_identity` — the algebraic engine;
* `weighted_chebyshev_sum` — for nonnegative weights and monovarying `f, g`,
  `(∑ wᵢfᵢ)(∑ wᵢgᵢ) ≤ (∑ wᵢ)·(∑ wᵢfᵢgᵢ)`;
* `weighted_chebyshev_sum_eq_iff` — the **exact equality characterisation**: equality
  holds iff for every pair `i, j ∈ s` one of `wᵢ = 0`, `wⱼ = 0`, `fᵢ = fⱼ`, `gᵢ = gⱼ`;
* `weighted_chebyshev_sum_eq_iff_const` — the textbook form for **strictly positive
  weights** and monotone sequences: equality holds iff `f` is constant on `s` *or* `g`
  is constant on `s`.

Specialising `wᵢ ≡ 1` recovers the unweighted statements of the parent file (then
`∑ wᵢ = #s`).
-/
import Mathlib

open Finset

namespace RearrangementWeightedChebyshev

variable {ι : Type*} {s : Finset ι} {w f g : ι → ℝ} {i j : ι}

/-- **Weighted discrete covariance identity.** For any real-valued `w, f, g` on a finite
set `s`, the symmetric weighted double sum `∑ᵢ∑ⱼ wᵢwⱼ(fᵢ − fⱼ)(gᵢ − gⱼ)` equals
`2·((∑ wᵢ)·(∑ wᵢfᵢgᵢ) − (∑ wᵢfᵢ)(∑ wᵢgᵢ))`. No sign or order hypotheses; this is the
algebraic heart of the weighted Chebyshev sum inequality. -/
theorem weighted_covariance_identity :
    ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j))
      = 2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * f i * g i)
        - (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)) := by
  have hinner : ∀ i, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j))
      = w i * f i * g i * (∑ j ∈ s, w j)
        - w i * f i * (∑ j ∈ s, w j * g j)
        - w i * g i * (∑ j ∈ s, w j * f j)
        + w i * (∑ j ∈ s, w j * f j * g j) := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hinner, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- The monovariation core: when `f` and `g` monovary on `s`, `(fᵢ − fⱼ)(gᵢ − gⱼ) ≥ 0`. -/
theorem monovary_term_nonneg (hfg : MonovaryOn f g s) (hi : i ∈ s) (hj : j ∈ s) :
    0 ≤ (f i - f j) * (g i - g j) := by
  rcases lt_trichotomy (g i) (g j) with h | h | h
  · have hf : f i ≤ f j := hfg hi hj h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f j - f i) (by linarith : (0:ℝ) ≤ g j - g i)]
  · have : g i - g j = 0 := by linarith
    rw [this, mul_zero]
  · have hf : f j ≤ f i := hfg hj hi h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f i - f j) (by linarith : (0:ℝ) ≤ g i - g j)]

/-- Each weighted summand is nonnegative when the weights are nonnegative and `f, g`
monovary. -/
theorem weighted_term_nonneg (hwi : 0 ≤ w i) (hwj : 0 ≤ w j) (hfg : MonovaryOn f g s)
    (hi : i ∈ s) (hj : j ∈ s) :
    0 ≤ w i * w j * ((f i - f j) * (g i - g j)) :=
  mul_nonneg (mul_nonneg hwi hwj) (monovary_term_nonneg hfg hi hj)

/-- **Weighted Chebyshev sum inequality**, derived from `weighted_covariance_identity`.
For nonnegative weights `w` and monovarying `f, g`,
`(∑ wᵢfᵢ)(∑ wᵢgᵢ) ≤ (∑ wᵢ)·(∑ wᵢfᵢgᵢ)`. -/
theorem weighted_chebyshev_sum (hw : ∀ i ∈ s, 0 ≤ w i) (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * f i * g i) := by
  have hsum : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      weighted_term_nonneg (hw i hi) (hw j hj) hfg hi hj
  rw [weighted_covariance_identity] at hsum
  linarith

/-- **Exact equality characterisation of the weighted Chebyshev sum inequality.** For
nonnegative weights `w` and monovarying `f, g`, equality
`(∑ wᵢ)·(∑ wᵢfᵢgᵢ) = (∑ wᵢfᵢ)(∑ wᵢgᵢ)` holds iff for every pair `i, j ∈ s` one of
`wᵢ = 0`, `wⱼ = 0`, `fᵢ = fⱼ`, `gᵢ = gⱼ` holds. -/
theorem weighted_chebyshev_sum_eq_iff (hw : ∀ i ∈ s, 0 ≤ w i) (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, w i) * (∑ i ∈ s, w i * f i * g i)
        = (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      ↔ ∀ i ∈ s, ∀ j ∈ s, w i = 0 ∨ w j = 0 ∨ f i = f j ∨ g i = g j := by
  have hid := weighted_covariance_identity (s := s) (w := w) (f := f) (g := g)
  rw [← sub_eq_zero]
  constructor
  · intro h
    have hzero : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) = 0 := by
      rw [hid, h]; ring
    intro i hi j hj
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => Finset.sum_nonneg fun j hj =>
        weighted_term_nonneg (hw i hi) (hw j hj) hfg hi hj)).mp hzero i hi
    have hterm : w i * w j * ((f i - f j) * (g i - g j)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j hj =>
        weighted_term_nonneg (hw i hi) (hw j hj) hfg hi hj).mp h1 j hj
    rcases mul_eq_zero.mp hterm with hww | hfgz
    · rcases mul_eq_zero.mp hww with hwi | hwj
      · exact Or.inl hwi
      · exact Or.inr (Or.inl hwj)
    · rcases mul_eq_zero.mp hfgz with hf | hg
      · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp hf)))
      · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp hg)))
  · intro h
    have hzero : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((f i - f j) * (g i - g j)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
      rcases h i hi j hj with hwi | hwj | hf | hg
      · rw [hwi]; ring
      · rw [hwj]; ring
      · rw [hf]; ring
      · rw [hg]; ring
    rw [hzero] at hid
    linarith

/-- **Equality case for strictly positive weights (textbook form).** If the weights are
strictly positive and `f, g : ι → ℝ` are monotone on a linearly ordered index type with
`s` nonempty, then equality in the weighted Chebyshev sum inequality holds iff `f` is
constant on `s` *or* `g` is constant on `s`. -/
theorem weighted_chebyshev_sum_eq_iff_const [LinearOrder ι] (hw : ∀ i ∈ s, 0 < w i)
    (hf : Monotone f) (hg : Monotone g) (hs : s.Nonempty) :
    (∑ i ∈ s, w i) * (∑ i ∈ s, w i * f i * g i)
        = (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)
      ↔ (∀ i ∈ s, ∀ j ∈ s, f i = f j) ∨ (∀ i ∈ s, ∀ j ∈ s, g i = g j) := by
  have hmono : MonovaryOn f g s := (hf.monovary hg).monovaryOn s
  rw [weighted_chebyshev_sum_eq_iff (fun i hi => (hw i hi).le) hmono]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨a, ha, b, hb, hfab⟩, ⟨c, hc, d, hd, hgcd⟩⟩ := hcon
    set m := s.min' hs with hm_def
    set M := s.max' hs with hM_def
    have hm : m ∈ s := s.min'_mem hs
    have hM : M ∈ s := s.max'_mem hs
    have hfmM : f m ≠ f M := fun he => hfab (by
      have l1 : f m ≤ f a := hf (s.min'_le a ha)
      have l2 : f a ≤ f M := hf (s.le_max' a ha)
      have l3 : f m ≤ f b := hf (s.min'_le b hb)
      have l4 : f b ≤ f M := hf (s.le_max' b hb)
      linarith)
    have hgmM : g m ≠ g M := fun he => hgcd (by
      have l1 : g m ≤ g c := hg (s.min'_le c hc)
      have l2 : g c ≤ g M := hg (s.le_max' c hc)
      have l3 : g m ≤ g d := hg (s.min'_le d hd)
      have l4 : g d ≤ g M := hg (s.le_max' d hd)
      linarith)
    rcases h m hm M hM with hwm | hwM | hfe | hge
    · exact absurd hwm (hw m hm).ne'
    · exact absurd hwM (hw M hM).ne'
    · exact hfmM hfe
    · exact hgmM hge
  · rintro (hfc | hgc) i hi j hj
    · exact Or.inr (Or.inr (Or.inl (hfc i hi j hj)))
    · exact Or.inr (Or.inr (Or.inr (hgc i hi j hj)))

end RearrangementWeightedChebyshev
