import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic

/-
# Modified Dirichlet Function (Thomae's Function) — Lebesgue Integral

## What This Proves

The modified Dirichlet function (also known as Thomae's function or the
popcorn function):

  f(x) = 1/q  if x = p/q in lowest terms (q > 0)
  f(x) = 0    if x is irrational

has Lebesgue integral 0 over [0,1].

## Key Facts

- f is discontinuous at every rational, continuous at every irrational
- f is Riemann integrable (unlike the standard Dirichlet function)
- The Lebesgue integral is 0 because f = 0 a.e. (rationals have measure 0)

## Proof Strategy

1. f is zero on irrationals (the irrationals have full measure)
2. The rationals have measure zero (from LebesgueMeasureOQ01)
3. Therefore f = 0 a.e., and ∫ f = 0

## Open Question Origin

From the Lebesgue Measure gallery proof (lebesgue-measure-oq-01):
"Can the modified Dirichlet function f(x) = 1/q for x = p/q in lowest
terms be shown to have Lebesgue integral 0 using the same a.e. argument?"

Answer: YES. This file provides the proof.
-/

open MeasureTheory Measure Set Filter

namespace LebesgueMeasureOQ01OQ01

/-
## Part I: The Modified Dirichlet (Thomae) Function
-/

/-- The modified Dirichlet function (Thomae's function):
    f(x) = 1/q if x = p/q in lowest terms, f(x) = 0 if x is irrational.

    We define this as a function ℝ → ℝ using Lean's classical choice:
    if x ∈ range(Rat.cast), extract the rational and return 1/den,
    otherwise return 0. -/
noncomputable def thomae : ℝ → ℝ := fun x =>
  if h : ∃ q : ℚ, (q : ℝ) = x then
    1 / (h.choose.den : ℝ)
  else
    0

/-- Thomae's function is zero at irrational points. -/
theorem thomae_irrational {x : ℝ} (hx : Irrational x) : thomae x = 0 := by
  unfold thomae
  rw [dif_neg]
  intro ⟨q, hq⟩
  exact hx ⟨q, hq.symm⟩

/-- Thomae's function is nonneg everywhere. -/
theorem thomae_nonneg (x : ℝ) : 0 ≤ thomae x := by
  unfold thomae
  split
  · positivity
  · le_refl

/-- Thomae's function is bounded above by 1. -/
theorem thomae_le_one (x : ℝ) : thomae x ≤ 1 := by
  unfold thomae
  split
  · have hden : (0 : ℝ) < ↑(Exists.choose ‹_›).den := by positivity
    exact div_le_one_of_le (le_of_eq rfl) (le_of_lt hden)
  · linarith

/-
## Part II: Thomae's Function is Zero Almost Everywhere
-/

/-- The set where Thomae's function is nonzero is contained in the rationals. -/
theorem thomae_support_subset_rationals :
    {x : ℝ | thomae x ≠ 0} ⊆ Set.range (Rat.cast : ℚ → ℝ) := by
  intro x hx
  unfold thomae at hx
  by_contra h
  rw [Set.mem_range] at h
  push_neg at h
  simp only [dif_neg (show ¬∃ q : ℚ, (q : ℝ) = x from h)] at hx

/-- Thomae's function is zero almost everywhere (w.r.t. Lebesgue measure).
    Proof: the support is contained in ℚ, which has measure zero. -/
theorem thomae_ae_zero : ∀ᵐ x ∂volume, thomae x = 0 := by
  rw [Filter.Eventually, ae_iff]
  suffices h : volume {x : ℝ | thomae x ≠ 0} = 0 from h
  exact measure_mono_null thomae_support_subset_rationals
    (Set.Countable.measure_zero (Set.countable_range _) volume)

/-
## Part III: The Lebesgue Integral
-/

/-- **Main Result**: The Lebesgue integral of Thomae's function over ℝ is 0. -/
theorem thomae_integral_zero : ∫ x, thomae x ∂volume = 0 := by
  exact integral_eq_zero_of_ae thomae_ae_zero

/-- The Lebesgue integral of Thomae's function over [0,1] is 0.
    (Restricted to the standard interval for textbook presentation.) -/
theorem thomae_integral_unit_interval :
    ∫ x in Set.Icc (0 : ℝ) 1, thomae x ∂volume = 0 := by
  apply integral_eq_zero_of_ae
  exact ae_restrict_of_ae thomae_ae_zero

/-
## Part IV: Comparison with Standard Dirichlet Function
-/

/-- The standard Dirichlet function (indicator of ℚ). -/
noncomputable def dirichlet : ℝ → ℝ := fun x =>
  if ∃ q : ℚ, (q : ℝ) = x then 1 else 0

/-- Thomae's function is pointwise ≤ the Dirichlet function. -/
theorem thomae_le_dirichlet (x : ℝ) : thomae x ≤ dirichlet x := by
  unfold thomae dirichlet
  split
  · split
    · exact div_le_one_of_le (le_of_eq rfl) (by positivity)
    · exact absurd ‹_› ‹_›
  · split
    · linarith
    · le_refl

/-- Both functions have the same Lebesgue integral (zero). -/
theorem dirichlet_integral_zero : ∫ x, dirichlet x ∂volume = 0 := by
  apply integral_eq_zero_of_ae
  rw [Filter.Eventually, ae_iff]
  suffices h : volume {x : ℝ | dirichlet x ≠ 0} = 0 from h
  apply measure_mono_null (show {x : ℝ | dirichlet x ≠ 0} ⊆ Set.range (Rat.cast : ℚ → ℝ) from ?_)
  · exact Set.Countable.measure_zero (Set.countable_range _) volume
  · intro x hx
    unfold dirichlet at hx
    by_contra h
    rw [Set.mem_range] at h
    push_neg at h
    simp only [dif_neg h] at hx

end LebesgueMeasureOQ01OQ01
