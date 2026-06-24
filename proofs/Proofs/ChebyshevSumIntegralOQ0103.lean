import Mathlib

/-
# Chebyshev's sum inequality, continuous (integral) form for monotone functions

The parent entry "Chebyshev's sum inequality in classical monotone-sequence form"
records the discrete inequality

  (∑ aᵢ)(∑ bᵢ) ≤ n · ∑ aᵢbᵢ                              (same monotonicity)

for two finite sequences sorted the same way, together with the open question of
formalising the **continuous (integral) Chebyshev inequality for monotone functions
on an interval**:

  (∫ₐᵇ f) (∫ₐᵇ g) ≤ (b − a) · ∫ₐᵇ f·g,                   (f, g both monotone)

with the inequality reversing when one function is increasing and the other decreasing.

## What this proves

`chebyshev_integral_monotoneOn` and `chebyshev_integral_antitoneOn` establish exactly
these two statements for `f g : ℝ → ℝ` that are both `MonotoneOn` (resp. `f` `MonotoneOn`,
`g` `AntitoneOn`) on `Set.Icc a b`, stated with the Lebesgue interval integral `∫ x in a..b`.

## Relation to the gallery

The gallery already contains the *general* comonotone integral inequality
(`chebyshev-sum-inequality-oq-01-oq-01-oq-01`, `chebyshev_integral_mul_le`): for a finite
measure `μ` and **bounded measurable** functions satisfying the **global** comonotonicity
hypothesis `∀ x y, 0 ≤ (f x − f y)(g x − g y)`, `(∫f)(∫g) ≤ μ(univ)·∫fg`. That statement
does *not* directly give the classical monotone-functions-on-an-interval form posed by the
parent's open question: a `MonotoneOn` function on `Icc a b` is monotone only *locally*
(its comonotonicity holds only on the interval, not on all of `ℝ`), and need be neither
globally bounded nor globally measurable. This entry supplies that form, discharging
integrability and the comonotone sign directly from `MonotoneOn`, and packaging the result
with the everyday interval integral `∫ x in a..b`.

## Method

Mathlib has Chebyshev's inequality for **finite sums** (`Mathlib/Algebra/Order/Chebyshev.lean`,
via `MonovaryOn`) but **no integral version**. As in the general entry, the continuous
statement follows from the classical two-variable identity

  ∫∫_{[a,b]²} (f x − f y)(g x − g y) d(x,y) = 2 (b − a) ∫ f·g − 2 (∫ f)(∫ g),

whose left-hand side is `≥ 0` because the integrand is pointwise nonnegative when `f` and
`g` are monotone the same way (both factors share their sign). We realise the square as the
product measure `μ.prod μ` with `μ = volume.restrict (Icc a b)` and evaluate the four
cross terms with `MeasureTheory.integral_prod_mul`, `integral_fun_fst`, `integral_fun_snd`.
The new ingredient over the general entry is the bridge from `MonotoneOn` to integrability
(`MonotoneOn.integrableOn_of_measure_ne_top`, no boundedness hypothesis) and to the a.e.
sign on the square (`Measure.prod_restrict`, `ae_restrict_iff'`).

## Mathlib ingredients
- `MeasureTheory.integral_prod_mul`, `integral_fun_fst`, `integral_fun_snd` (Fubini products)
- `MonotoneOn.integrableOn_of_measure_ne_top` (monotone ⇒ integrable on a finite interval)
- `MeasureTheory.Integrable.mul_prod`, `Integrable.comp_fst_iff`, `Integrable.comp_snd_iff`
- `MeasureTheory.integral_nonneg_of_ae`, `Measure.prod_restrict`, `ae_restrict_iff'`

All results are fully verified with no extra axioms.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ChebyshevIntegralMonotone

variable {a b : ℝ} {f g : ℝ → ℝ}

/-- Pointwise nonnegativity of the symmetrised integrand for two functions that are
monotone the same way: if `f` and `g` are both `MonotoneOn (Icc a b)` then
`0 ≤ (f x − f y)(g x − g y)` for `x, y ∈ Icc a b`. -/
theorem sub_mul_sub_nonneg_of_monotoneOn
    (hf : MonotoneOn f (Icc a b)) (hg : MonotoneOn g (Icc a b))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    0 ≤ (f x - f y) * (g x - g y) := by
  rcases le_total x y with h | h
  · have hf' : f x ≤ f y := hf hx hy h
    have hg' : g x ≤ g y := hg hx hy h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f y - f x) (by linarith : (0:ℝ) ≤ g y - g x)]
  · have hf' : f y ≤ f x := hf hy hx h
    have hg' : g y ≤ g x := hg hy hx h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f x - f y) (by linarith : (0:ℝ) ≤ g x - g y)]

/-- A `MonotoneOn` function on `Icc a b` is bounded there by `max |f a| |f b|`. -/
theorem norm_le_of_monotoneOn (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) :
    ∀ᵐ x ∂(volume.restrict (Icc a b)), ‖f x‖ ≤ max |f a| |f b| := by
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall ?_)
  intro x hx
  have hfa : f a ≤ f x := hf (left_mem_Icc.mpr hab) hx hx.1
  have hfb : f x ≤ f b := hf hx (right_mem_Icc.mpr hab) hx.2
  rw [Real.norm_eq_abs, abs_le]
  refine ⟨?_, ?_⟩
  · calc -max |f a| |f b| ≤ -|f a| := neg_le_neg (le_max_left |f a| |f b|)
      _ ≤ f a := neg_abs_le _
      _ ≤ f x := hfa
  · calc f x ≤ f b := hfb
      _ ≤ |f b| := le_abs_self _
      _ ≤ max |f a| |f b| := le_max_right _ _

/-- **Continuous Chebyshev sum inequality (set-integral form).**
If `f` and `g` are both monotone on `Icc a b` (and `a ≤ b`), then
`(∫ f)(∫ g) ≤ (b − a) ∫ f·g`, the integrals being over `Icc a b`. -/
theorem chebyshev_integral_monotoneOn_setIntegral
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hg : MonotoneOn g (Icc a b)) :
    (∫ x in Icc a b, f x) * (∫ x in Icc a b, g x)
      ≤ (b - a) * ∫ x in Icc a b, f x * g x := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · -- Degenerate interval: every integral vanishes.
    subst heq
    have h0 : volume.restrict (Icc a a) = (0 : Measure ℝ) := by
      rw [Measure.restrict_eq_zero, Real.volume_Icc, sub_self, ENNReal.ofReal_zero]
    rw [h0]
    simp
  · -- Main case `a < b`.
    set μ : Measure ℝ := volume.restrict (Icc a b) with hμdef
    have hμtop : volume (Icc a b) ≠ ∞ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    haveI hfin : IsFiniteMeasure μ := by
      refine ⟨?_⟩
      rw [hμdef, Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr hμtop
    have hmass : μ.real univ = b - a := by
      rw [hμdef, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)]
    have hμne : μ ≠ 0 := by
      rw [hμdef, Ne, Measure.restrict_eq_zero, Real.volume_Icc, ENNReal.ofReal_eq_zero, not_le]
      linarith
    -- Integrability of `f`, `g`, `f·g` against `μ`.
    have hfI : Integrable f μ :=
      hf.integrableOn_of_measure_ne_top (isLeast_Icc hab) (isGreatest_Icc hab)
        hμtop measurableSet_Icc
    have hgI : Integrable g μ :=
      hg.integrableOn_of_measure_ne_top (isLeast_Icc hab) (isGreatest_Icc hab)
        hμtop measurableSet_Icc
    have hfgI : Integrable (fun x => f x * g x) μ :=
      hfI.mul_bdd hgI.aestronglyMeasurable (hμdef ▸ norm_le_of_monotoneOn hab hg)
    -- Integrability of the four cross terms against the product measure.
    have ip1 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.1) (μ.prod μ) :=
      (Integrable.comp_fst_iff hμne).mpr hfgI
    have ip2 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2) (μ.prod μ) := hfI.mul_prod hgI
    have ip3 : Integrable (fun z : ℝ × ℝ => g z.1 * f z.2) (μ.prod μ) := hgI.mul_prod hfI
    have ip4 : Integrable (fun z : ℝ × ℝ => f z.2 * g z.2) (μ.prod μ) :=
      (Integrable.comp_snd_iff hμne).mpr hfgI
    -- The symmetrised double integral equals `2(b-a)∫fg − 2(∫f)(∫g)`.
    have key : ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ)
        = 2 * ((b - a) * ∫ x, f x * g x ∂μ)
          - 2 * ((∫ x, f x ∂μ) * (∫ x, g x ∂μ)) := by
      have hexp : (fun z : ℝ × ℝ => (f z.1 - f z.2) * (g z.1 - g z.2))
          = fun z => (f z.1 * g z.1 + f z.2 * g z.2) - (f z.1 * g z.2 + g z.1 * f z.2) := by
        funext z; ring
      have hF : Integrable (fun z : ℝ × ℝ => f z.1 * g z.1 + f z.2 * g z.2) (μ.prod μ) :=
        ip1.add ip4
      have hG : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2 + g z.1 * f z.2) (μ.prod μ) :=
        ip2.add ip3
      rw [hexp, integral_sub hF hG, integral_add ip1 ip4, integral_add ip2 ip3,
        integral_prod_mul (L := ℝ) f g, integral_prod_mul (L := ℝ) g f,
        integral_fun_fst (fun x => f x * g x), integral_fun_snd (fun x => f x * g x),
        hmass]
      simp only [smul_eq_mul]
      ring
    -- The double integral is nonnegative since the integrand is.
    have hae : 0 ≤ᵐ[μ.prod μ] fun z => (f z.1 - f z.2) * (g z.1 - g z.2) := by
      rw [hμdef, Measure.prod_restrict]
      refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).mpr
        (Filter.Eventually.of_forall ?_)
      intro z hz
      exact sub_mul_sub_nonneg_of_monotoneOn hf hg hz.1 hz.2
    have hnonneg : 0 ≤ ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ) :=
      integral_nonneg_of_ae hae
    rw [key] at hnonneg
    linarith

/-- **Reverse Chebyshev sum inequality (set-integral form).**
If `f` is monotone and `g` is antitone on `Icc a b` (and `a ≤ b`), then the inequality
reverses: `(b − a) ∫ f·g ≤ (∫ f)(∫ g)`. Obtained from the monotone case applied to `f`
and `-g`. -/
theorem chebyshev_integral_antitoneOn_setIntegral
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc a b)) :
    (b - a) * (∫ x in Icc a b, f x * g x)
      ≤ (∫ x in Icc a b, f x) * (∫ x in Icc a b, g x) := by
  have hgn : MonotoneOn (fun x => -g x) (Icc a b) := hg.neg
  have h := chebyshev_integral_monotoneOn_setIntegral hab hf hgn
  simp only [mul_neg, integral_neg] at h
  linarith

/-- **Continuous Chebyshev sum inequality, interval-integral form.**
For monotone `f, g` on `[a,b]` with `a ≤ b`:
`(∫ₐᵇ f)(∫ₐᵇ g) ≤ (b − a) ∫ₐᵇ f·g`. -/
theorem chebyshev_integral_monotoneOn
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hg : MonotoneOn g (Icc a b)) :
    (∫ x in a..b, f x) * (∫ x in a..b, g x)
      ≤ (b - a) * ∫ x in a..b, f x * g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc]
  exact chebyshev_integral_monotoneOn_setIntegral hab hf hg

/-- **Reverse Chebyshev sum inequality, interval-integral form.**
For `f` monotone and `g` antitone on `[a,b]` with `a ≤ b`:
`(b − a) ∫ₐᵇ f·g ≤ (∫ₐᵇ f)(∫ₐᵇ g)`. -/
theorem chebyshev_integral_antitoneOn
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc a b)) :
    (b - a) * (∫ x in a..b, f x * g x)
      ≤ (∫ x in a..b, f x) * (∫ x in a..b, g x) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc]
  exact chebyshev_integral_antitoneOn_setIntegral hab hf hg

end ChebyshevIntegralMonotone
