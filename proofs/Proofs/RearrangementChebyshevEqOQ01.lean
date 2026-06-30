/-
# Equality case of Chebyshev's sum inequality (the discrete covariance identity)

Mathlib proves Chebyshev's sum inequality
(`MonovaryOn.sum_mul_sum_le_card_mul_sum` in `Mathlib/Algebra/Order/Chebyshev.lean`):
when `f` and `g` monovary on a finite set `s`,
  `(∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ #s * ∑ i ∈ s, f i * g i`.
It does **not** record *when equality holds*, nor the two-index algebraic identity
that drives the inequality.

This file fills that gap. The engine is the **discrete covariance identity**
  `∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j)
      = 2 * (#s * (∑ i ∈ s, f i * g i) - (∑ i ∈ s, f i) * (∑ i ∈ s, g i))`,
valid for *any* real-valued `f, g` (no monotonicity assumption). It is the finite,
unnormalised analogue of `2 · n² · Cov(f, g)`.

From it we obtain, with zero extra axioms:
* `chebyshev_sum` — Chebyshev's inequality, re-derived from the identity;
* `chebyshev_sum_eq_iff` — the **exact equality characterisation**: for monovarying
  `f, g`, equality holds iff for every pair `i, j ∈ s` either `f i = f j` or `g i = g j`;
* `chebyshev_sum_eq_iff_const` — the textbook form for **monotone** sequences: equality
  holds iff `f` is constant on `s` *or* `g` is constant on `s`.

The last step is the "extreme pair" argument: a monotone non-constant function already
differs between `min' s` and `max' s`, so if both `f` and `g` varied, the `(min', max')`
term would be strictly positive.
-/
import Mathlib

open Finset

namespace RearrangementChebyshevEq

variable {ι : Type*} {s : Finset ι} {f g : ι → ℝ}

/-- **Discrete covariance identity.** For any real-valued `f, g` on a finite set `s`,
the symmetric double sum `∑ᵢ∑ⱼ (fᵢ - fⱼ)(gᵢ - gⱼ)` equals
`2 · (#s · ∑ fᵢgᵢ − (∑ fᵢ)(∑ gᵢ))`. This is the algebraic heart of Chebyshev's sum
inequality and is the finite analogue of `2 n² · Cov(f, g)`. No order hypotheses. -/
theorem covariance_identity :
    ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j)
      = 2 * ((s.card : ℝ) * (∑ i ∈ s, f i * g i)
        - (∑ i ∈ s, f i) * (∑ i ∈ s, g i)) := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Each summand of the covariance double sum is nonnegative when `f` and `g` monovary. -/
theorem term_nonneg (hfg : MonovaryOn f g s) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    0 ≤ (f i - f j) * (g i - g j) := by
  rcases lt_trichotomy (g i) (g j) with h | h | h
  · have hf : f i ≤ f j := hfg hi hj h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f j - f i) (by linarith : (0:ℝ) ≤ g j - g i)]
  · have : g i - g j = 0 := by linarith
    rw [this, mul_zero]
  · have hf : f j ≤ f i := hfg hj hi h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f i - f j) (by linarith : (0:ℝ) ≤ g i - g j)]

/-- **Chebyshev's sum inequality**, re-derived from `covariance_identity`. When `f` and `g`
monovary on `s`, `(∑ f)(∑ g) ≤ #s · ∑ f·g`. (Mathlib's `MonovaryOn.sum_mul_sum_le_card_mul_sum`
states the same bound; here it is a one-line corollary of the identity.) -/
theorem chebyshev_sum (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ (s.card : ℝ) * ∑ i ∈ s, f i * g i := by
  have hsum : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => term_nonneg hfg hi hj
  rw [covariance_identity] at hsum
  linarith

/-- **Exact equality characterisation of Chebyshev's sum inequality.** For `f, g` monovarying
on `s`, equality `#s · ∑ f·g = (∑ f)(∑ g)` holds iff for every pair `i, j ∈ s` we have
`f i = f j` or `g i = g j` (i.e. no pair witnesses strict comonotonicity). -/
theorem chebyshev_sum_eq_iff (hfg : MonovaryOn f g s) :
    (s.card : ℝ) * (∑ i ∈ s, f i * g i) = (∑ i ∈ s, f i) * (∑ i ∈ s, g i)
      ↔ ∀ i ∈ s, ∀ j ∈ s, f i = f j ∨ g i = g j := by
  have hid := covariance_identity (s := s) (f := f) (g := g)
  rw [← sub_eq_zero]
  constructor
  · intro h
    have hzero : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) = 0 := by rw [hid, h]; ring
    intro i hi j hj
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => Finset.sum_nonneg fun j hj => term_nonneg hfg hi hj)).mp hzero i hi
    have hterm : (f i - f j) * (g i - g j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j hj => term_nonneg hfg hi hj).mp h1 j hj
    rcases mul_eq_zero.mp hterm with hf | hg
    · exact Or.inl (sub_eq_zero.mp hf)
    · exact Or.inr (sub_eq_zero.mp hg)
  · intro h
    have hzero : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) = 0 := by
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
      rcases h i hi j hj with hf | hg
      · rw [hf]; ring
      · rw [hg]; ring
    rw [hzero] at hid
    linarith

/-- **Equality case for monotone sequences (textbook form).** If `f, g : ι → ℝ` are monotone
on a linearly ordered index type and `s` is nonempty, then equality in Chebyshev's sum
inequality holds iff `f` is constant on `s` *or* `g` is constant on `s`. -/
theorem chebyshev_sum_eq_iff_const [LinearOrder ι] (hf : Monotone f) (hg : Monotone g)
    (hs : s.Nonempty) :
    (s.card : ℝ) * (∑ i ∈ s, f i * g i) = (∑ i ∈ s, f i) * (∑ i ∈ s, g i)
      ↔ (∀ i ∈ s, ∀ j ∈ s, f i = f j) ∨ (∀ i ∈ s, ∀ j ∈ s, g i = g j) := by
  have hmono : MonovaryOn f g s := (hf.monovary hg).monovaryOn s
  rw [chebyshev_sum_eq_iff hmono]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨a, ha, b, hb, hfab⟩, ⟨c, hc, d, hd, hgcd⟩⟩ := hcon
    set m := s.min' hs with hm_def
    set M := s.max' hs with hM_def
    have hm : m ∈ s := s.min'_mem hs
    have hM : M ∈ s := s.max'_mem hs
    -- `f` non-constant forces `f m ≠ f M`; likewise for `g`.
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
    rcases h m hm M hM with hfe | hge
    · exact hfmM hfe
    · exact hgmM hge
  · rintro (hfc | hgc) i hi j hj
    · exact Or.inl (hfc i hi j hj)
    · exact Or.inr (hgc i hi j hj)

end RearrangementChebyshevEq
