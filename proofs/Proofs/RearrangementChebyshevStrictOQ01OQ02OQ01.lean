/-
# Strict *reverse* Chebyshev sum inequality (the antivarying / mixed-monotone case)

The parent file `RearrangementChebyshevStrictOQ01OQ02` proves the **strict** Chebyshev
sum inequality for **monovarying** (e.g. both monotone) sequences:
`(∑ f)(∑ g) < #s · ∑ f·g` unless one sequence is constant.

This file answers the parent's open question by treating the **opposite** ordering
regime — `f` and `g` **antivary** (the textbook case "`f` increasing, `g` decreasing").
There the inequality reverses:

    #s · ∑ f·g  ≤  (∑ f)(∑ g),

with equality iff one sequence is constant; otherwise the inequality is **strict**:

    #s · ∑ f·g  <  (∑ f)(∑ g)      i.e.   (∑ f)(∑ g) > #s · ∑ f·g.

## Mechanism — the same order-free covariance identity

Everything rides on the grandparent's `covariance_identity` (no order hypotheses):

    ∑ᵢ∑ⱼ (fᵢ − fⱼ)(gᵢ − gⱼ) = 2·(#s·∑ fᵢgᵢ − (∑ fᵢ)(∑ gᵢ)).

For **antivarying** `f, g` each summand `(fᵢ − fⱼ)(gᵢ − gⱼ)` is **non-positive**
(`term_nonpos`), so the double sum is `≤ 0`, which is exactly the reverse bound. A single
pair with both coordinates varying makes one summand strictly negative, forcing strictness.
Note the equality *characterisation* — `∀ i j, fᵢ = fⱼ ∨ gᵢ = gⱼ` — is **identical** to the
monovarying case, because a product of two reals is `0` regardless of the signs of the
factors; only the *inequality direction* flips.

## Main results

* `term_nonpos` — each covariance summand is `≤ 0` when `f, g` antivary on `s`.
* `chebyshev_sum_reverse` — the reverse bound `#s·∑ f·g ≤ (∑ f)(∑ g)` for `AntivaryOn f g s`.
* `chebyshev_sum_reverse_eq_iff` — equality holds iff every pair `i, j ∈ s` satisfies
  `f i = f j ∨ g i = g j` (same characterisation as the monovarying case).
* `chebyshev_sum_reverse_eq_iff_const` — textbook form: for `f` monotone and `g` antitone on
  a linearly ordered index with `s` nonempty, equality holds iff `f` or `g` is constant on `s`.
* `chebyshev_sum_reverse_strict_of_pair` — the general antivariance form: one pair `a, b ∈ s`
  with `f a ≠ f b` *and* `g a ≠ g b` already forces `(∑ f)(∑ g) > #s·∑ f·g`.
* `chebyshev_sum_reverse_strict` — textbook strict form: `f` monotone, `g` antitone, `s`
  nonempty, neither constant ⟹ `(∑ f)(∑ g) > #s·∑ f·g`.
* `chebyshev_sum_reverse_strict_strictMonoAnti` — cleanest specialisation: `f` strictly
  monotone, `g` strictly antitone, `1 < #s` ⟹ strict.

Each strict result is `lt_of_le_of_ne` applied to the reverse `≤` and the negation of the
equality characterisation; no new axioms are introduced.

References:
- Parent: `chebyshev-sum-inequality-oq-01-oq-02` (`RearrangementChebyshevStrictOQ01OQ02`,
  the monovarying strict form).
- Grandparent: `RearrangementChebyshevEqOQ01` (`covariance_identity`, equality machinery).
- Mathlib `Mathlib/Order/Monotone/Monovary.lean` (`AntivaryOn`, `Monotone.antivary`).
-/
import Mathlib
import Proofs.RearrangementChebyshevStrictOQ01OQ02

open Finset

namespace RearrangementChebyshevReverse

open RearrangementChebyshevEq

variable {ι : Type*} {s : Finset ι} {f g : ι → ℝ}

/-- **Non-positivity of the covariance summand under antivariance.** If `f` and `g` antivary
on `s`, then for `i, j ∈ s` the term `(f i − f j)(g i − g j) ≤ 0`: when `g` increases across a
pair, `f` weakly decreases (and vice versa), so the two differences have opposite signs. This
is the antivarying mirror of the grandparent's `term_nonneg`. -/
theorem term_nonpos (hfg : AntivaryOn f g s) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (f i - f j) * (g i - g j) ≤ 0 := by
  rcases lt_trichotomy (g i) (g j) with h | h | h
  · -- `g i < g j` ⟹ `f j ≤ f i`: first factor `≥ 0`, second `< 0`.
    have hf : f j ≤ f i := hfg hi hj h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f i - f j) (by linarith : (0:ℝ) ≤ g j - g i)]
  · have : g i - g j = 0 := by linarith
    rw [this, mul_zero]
  · -- `g j < g i` ⟹ `f i ≤ f j`: first factor `≤ 0`, second `> 0`.
    have hf : f i ≤ f j := hfg hj hi h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f j - f i) (by linarith : (0:ℝ) ≤ g i - g j)]

/-- **Reverse Chebyshev sum inequality.** When `f` and `g` antivary on `s`,
`#s · ∑ f·g ≤ (∑ f)(∑ g)` — the inequality of the monovarying case run backwards. One line
from `covariance_identity`, whose double sum is now `≤ 0`. -/
theorem chebyshev_sum_reverse (hfg : AntivaryOn f g s) :
    (s.card : ℝ) * (∑ i ∈ s, f i * g i) ≤ (∑ i ∈ s, f i) * (∑ i ∈ s, g i) := by
  have hsum : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) ≤ 0 :=
    Finset.sum_nonpos fun i hi => Finset.sum_nonpos fun j hj => term_nonpos hfg hi hj
  rw [covariance_identity] at hsum
  linarith

/-- **Exact equality characterisation of the reverse inequality.** For `f, g` antivarying on
`s`, equality `#s · ∑ f·g = (∑ f)(∑ g)` holds iff every pair `i, j ∈ s` has `f i = f j` or
`g i = g j`. This is the *same* condition as in the monovarying case: a product vanishes
exactly when a factor does, independent of sign. -/
theorem chebyshev_sum_reverse_eq_iff (hfg : AntivaryOn f g s) :
    (s.card : ℝ) * (∑ i ∈ s, f i * g i) = (∑ i ∈ s, f i) * (∑ i ∈ s, g i)
      ↔ ∀ i ∈ s, ∀ j ∈ s, f i = f j ∨ g i = g j := by
  have hid := covariance_identity (s := s) (f := f) (g := g)
  rw [← sub_eq_zero]
  constructor
  · intro h
    have hzero : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) = 0 := by rw [hid]; linarith
    intro i hi j hj
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos
      (fun i hi => Finset.sum_nonpos fun j hj => term_nonpos hfg hi hj)).mp hzero i hi
    have hterm : (f i - f j) * (g i - g j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos fun j hj => term_nonpos hfg hi hj).mp h1 j hj
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

/-- **Equality case for `f` monotone, `g` antitone (textbook form).** On a linearly ordered
index with `s` nonempty, equality in the reverse inequality holds iff `f` is constant on `s`
*or* `g` is constant on `s`. The extreme-pair argument: a monotone non-constant `f` already
differs between `min' s` and `max' s`; an antitone non-constant `g` likewise. -/
theorem chebyshev_sum_reverse_eq_iff_const [LinearOrder ι] (hf : Monotone f) (hg : Antitone g)
    (hs : s.Nonempty) :
    (s.card : ℝ) * (∑ i ∈ s, f i * g i) = (∑ i ∈ s, f i) * (∑ i ∈ s, g i)
      ↔ (∀ i ∈ s, ∀ j ∈ s, f i = f j) ∨ (∀ i ∈ s, ∀ j ∈ s, g i = g j) := by
  have hanti : AntivaryOn f g s := (hf.antivary hg).antivaryOn s
  rw [chebyshev_sum_reverse_eq_iff hanti]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨a, ha, b, hb, hfab⟩, ⟨c, hc, d, hd, hgcd⟩⟩ := hcon
    set m := s.min' hs with hm_def
    set M := s.max' hs with hM_def
    have hm : m ∈ s := s.min'_mem hs
    have hM : M ∈ s := s.max'_mem hs
    -- `f` non-constant + monotone forces `f m ≠ f M`.
    have hfmM : f m ≠ f M := fun he => hfab (by
      have l1 : f m ≤ f a := hf (s.min'_le a ha)
      have l2 : f a ≤ f M := hf (s.le_max' a ha)
      have l3 : f m ≤ f b := hf (s.min'_le b hb)
      have l4 : f b ≤ f M := hf (s.le_max' b hb)
      linarith)
    -- `g` non-constant + antitone forces `g m ≠ g M` (inequalities point the other way).
    have hgmM : g m ≠ g M := fun he => hgcd (by
      have l1 : g c ≤ g m := hg (s.min'_le c hc)
      have l2 : g M ≤ g c := hg (s.le_max' c hc)
      have l3 : g d ≤ g m := hg (s.min'_le d hd)
      have l4 : g M ≤ g d := hg (s.le_max' d hd)
      linarith)
    rcases h m hm M hM with hfe | hge
    · exact hfmM hfe
    · exact hgmM hge
  · rintro (hfc | hgc) i hi j hj
    · exact Or.inl (hfc i hi j hj)
    · exact Or.inr (hgc i hi j hj)

/-- **Strict reverse Chebyshev inequality from a single doubly-varying pair.** If `f, g`
antivary on `s` and one pair `a, b ∈ s` has `f a ≠ f b` *and* `g a ≠ g b`, then
`(∑ f)(∑ g) > #s · ∑ f·g`. The pair alone breaks the equality characterisation. -/
theorem chebyshev_sum_reverse_strict_of_pair (hfg : AntivaryOn f g s)
    {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hfab : f a ≠ f b) (hgab : g a ≠ g b) :
    (s.card : ℝ) * (∑ i ∈ s, f i * g i) < (∑ i ∈ s, f i) * (∑ i ∈ s, g i) := by
  refine lt_of_le_of_ne (chebyshev_sum_reverse hfg) ?_
  intro heq
  have hpair := (chebyshev_sum_reverse_eq_iff hfg).mp heq a ha b hb
  rcases hpair with hf | hg
  · exact hfab hf
  · exact hgab hg

/-- **Strict reverse Chebyshev inequality for `f` monotone, `g` antitone (textbook form).** If
`f` is monotone, `g` is antitone on a linearly ordered index, `s` is nonempty, and neither is
constant on `s`, then `(∑ f)(∑ g) > #s · ∑ f·g` strictly. The single statement "the reverse
Chebyshev inequality is strict unless one sequence is constant". -/
theorem chebyshev_sum_reverse_strict [LinearOrder ι] (hf : Monotone f) (hg : Antitone g)
    (hs : s.Nonempty)
    (hf_nc : ∃ i ∈ s, ∃ j ∈ s, f i ≠ f j)
    (hg_nc : ∃ i ∈ s, ∃ j ∈ s, g i ≠ g j) :
    (s.card : ℝ) * (∑ i ∈ s, f i * g i) < (∑ i ∈ s, f i) * (∑ i ∈ s, g i) := by
  refine lt_of_le_of_ne (chebyshev_sum_reverse ((hf.antivary hg).antivaryOn s)) ?_
  intro heq
  rcases (chebyshev_sum_reverse_eq_iff_const hf hg hs).mp heq with hfc | hgc
  · obtain ⟨i, hi, j, hj, hij⟩ := hf_nc; exact hij (hfc i hi j hj)
  · obtain ⟨i, hi, j, hj, hij⟩ := hg_nc; exact hij (hgc i hi j hj)

/-- **Strict reverse Chebyshev inequality for strictly monotone `f`, strictly antitone `g`.**
With at least two indices the inequality is always strict: strict monotonicity/antitonicity
rule out constancy as soon as two distinct indices are present. -/
theorem chebyshev_sum_reverse_strict_strictMonoAnti [LinearOrder ι] (hf : StrictMono f)
    (hg : StrictAnti g) (hs : 1 < s.card) :
    (s.card : ℝ) * (∑ i ∈ s, f i * g i) < (∑ i ∈ s, f i) * (∑ i ∈ s, g i) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hs
  have hfab : f a ≠ f b := fun h => hab (hf.injective h)
  have hgab : g a ≠ g b := fun h => hab (hg.injective h)
  exact chebyshev_sum_reverse_strict hf.monotone hg.antitone ⟨a, ha⟩
    ⟨a, ha, b, hb, hfab⟩ ⟨a, ha, b, hb, hgab⟩

#check @term_nonpos
#check @chebyshev_sum_reverse
#check @chebyshev_sum_reverse_eq_iff
#check @chebyshev_sum_reverse_eq_iff_const
#check @chebyshev_sum_reverse_strict_of_pair
#check @chebyshev_sum_reverse_strict
#check @chebyshev_sum_reverse_strict_strictMonoAnti

end RearrangementChebyshevReverse
