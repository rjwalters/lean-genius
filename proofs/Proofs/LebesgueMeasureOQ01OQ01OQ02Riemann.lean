/-
  Thomae's Function is Riemann Integrable (integral 0)

  Open Question (lebesgue-measure-oq-01-oq-01-oq-02-oq-01):
  Show Thomae's (popcorn) function is Riemann integrable on [0,1] with integral 0.

  Strategy — the clean Lean route is NOT the textbook Lebesgue criterion.
  Mathlib does not expose a first-class `RiemannIntegrable` predicate or the
  Lebesgue criterion ("integrable ⇔ bounded and continuous a.e.") as a ready
  lemma; its `intervalIntegral` *is* the Bochner/Lebesgue integral. The direct
  route is:
    thomae =ᵐ[volume] 0,
  because `thomae x ≠ 0` only on the rationals — a countable (hence null) set.
  From a.e.-equality to 0 we get `Integrable thomae volume` (congr from
  `integrable_zero`) and `∫ x in (0:ℝ)..1, thomae x = 0` (interval `integral_congr_ae`).
  This sidesteps the missing Lebesgue-criterion machinery entirely.

  Parent: `proofs/Proofs/LebesgueMeasureOQ01OQ01OQ02.lean` (0-sorry) supplies
  `thomae` and `thomae_irrational : Irrational x → thomae x = 0`. The crucial fact
  here is the cheap `thomae_irrational` (nonzero ⊆ ℚ ⟹ a.e. zero), not the
  continuity results.

  No sorries, no axioms.
-/
import Mathlib
import Proofs.LebesgueMeasureOQ01OQ01OQ02

open MeasureTheory Set
open LebesgueMeasureOQ01OQ01OQ02

namespace LebesgueMeasureOQ01OQ01OQ02Riemann

/-- The support of Thomae's function lies in the image of `ℚ` in `ℝ`:
    `thomae x ≠ 0` forces `x` to be rational. (`Irrational x` is by definition
    `x ∉ Set.range ((↑) : ℚ → ℝ)`, so the `by_contra` hypothesis feeds
    `thomae_irrational` directly.) -/
theorem thomae_support_subset_rat :
    {x : ℝ | thomae x ≠ 0} ⊆ Set.range ((↑) : ℚ → ℝ) := by
  intro x hx
  by_contra h
  exact hx (thomae_irrational h)

/-- The support of Thomae's function is null: it is contained in the countable
    set `Set.range ((↑) : ℚ → ℝ)`, which has measure zero under `volume`
    (`NoAtoms`). -/
theorem thomae_support_null : volume {x : ℝ | thomae x ≠ 0} = 0 :=
  measure_mono_null thomae_support_subset_rat
    ((Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume)

/-- Thomae's function is `volume`-a.e. equal to the zero function. -/
theorem thomae_ae_eq_zero : thomae =ᵐ[volume] 0 := by
  refine (ae_iff).mpr ?_
  simp only [Pi.zero_apply, ne_eq]
  exact thomae_support_null

/-- Thomae's function is integrable (it agrees a.e. with the zero function). -/
theorem thomae_integrable : Integrable thomae volume :=
  (integrable_zero ℝ ℝ volume).congr thomae_ae_eq_zero.symm

/-- The (Bochner/Lebesgue = Riemann) integral of Thomae's function over `[0,1]`
    is `0`. -/
theorem thomae_intervalIntegral_zero :
    ∫ x in (0:ℝ)..1, thomae x = 0 := by
  have h : (∫ x in (0:ℝ)..1, thomae x) = ∫ _ in (0:ℝ)..1, (0:ℝ) :=
    intervalIntegral.integral_congr_ae (thomae_ae_eq_zero.mono (fun x hx _ => hx))
  rw [h, intervalIntegral.integral_zero]

end LebesgueMeasureOQ01OQ01OQ02Riemann
