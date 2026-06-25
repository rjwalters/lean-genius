import Mathlib
import Proofs.BuffonsNeedleOQ01OQ01

/-!
# Buffon–Barbier: Discharging the Integrability Hypothesis from C¹ Smoothness

`BuffonsNeedleOQ01OQ01.lean` proves the Buffon–Barbier smooth-curve formula

  `concreteSmoothExpectedCrossings γ a b d = 2 · planarArcLength γ a b / (π·d)`

but leaves the analytic regularity packaged as **hypotheses** of
`buffon_smooth_full`:

* `hdx`, `hdy` — differentiability of the two coordinate functions (the C¹ assumption);
* `hInnerInt` — *interval-integrability* of the inner angular integral
  `t ↦ ∫₀^π |γ'₁(t)·sin θ + γ'₂(t)·cos θ| dθ` as a function of `t`.

The fifth open question of the parent entry asks to *"prove the co-area formula
in Mathlib to eliminate the Fubini hypothesis"*. The full co-area formula remains
open in Mathlib. This file resolves the **concrete, Buffon-specific residue** of
that question: it discharges `hInnerInt` directly from continuity of the velocity
field, with **no integrability assumption left**.

## The mathematical content

The map `t ↦ ∫₀^π |A(t)·sin θ + B(t)·cos θ| dθ` is **continuous** whenever `A`, `B`
are continuous, because the integrand `(t, θ) ↦ |A(t)·sin θ + B(t)·cos θ|` is jointly
continuous and the integration interval `[0, π]` is fixed and compact (Mathlib's
`continuous_parametric_intervalIntegral_of_continuous'`). Continuity on the compact
interval `[a, b]` upgrades to interval-integrability. No closed form, dominated
convergence bookkeeping, or co-area machinery is required.

Feeding this into `buffon_smooth_full` yields `buffon_smooth_C1`: the Buffon–Barbier
identity for an arbitrary C¹ planar curve whose velocity is continuous, with the
integrability hypothesis fully removed.

## Honest scope

This is **not** the general co-area / Cauchy–Crofton formula. It eliminates exactly
one of the two analytic side conditions (`hInnerInt`) of the parent theorem, leaving
only the differentiability hypotheses `hdx`/`hdy`, which *are* the bare C¹ assumption.
The general co-area formula in arbitrary dimension remains an open Mathlib target.
-/

open Real intervalIntegral MeasureTheory

namespace BuffonsNeedleOQ01OQ01OQ05

/-- The **inner angular integral** as a function of the coefficient functions:
`t ↦ ∫₀^π |A(t)·sin θ + B(t)·cos θ| dθ`. This is precisely the integrand of the
outer integral in `concreteSmoothExpectedCrossings`, with `A = γ'₁`, `B = γ'₂`. -/
noncomputable def innerAngular (A B : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..π, |A t * sin θ + B t * cos θ|

/-- **Continuity of the inner angular integral.**
If the coefficient functions `A` and `B` are continuous, then the inner angular
integral `t ↦ ∫₀^π |A(t)·sin θ + B(t)·cos θ| dθ` is continuous.

The integrand `(t, θ) ↦ |A(t)·sin θ + B(t)·cos θ|` is jointly continuous, and the
interval of integration `[0, π]` is fixed; continuity of the parametric interval
integral is then `continuous_parametric_intervalIntegral_of_continuous'`. -/
theorem innerAngular_continuous (A B : ℝ → ℝ) (hA : Continuous A) (hB : Continuous B) :
    Continuous (innerAngular A B) := by
  unfold innerAngular
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have : Continuous (Function.uncurry fun t θ => |A t * sin θ + B t * cos θ|) := by
    unfold Function.uncurry
    fun_prop
  exact this

/-- **Interval-integrability of the inner angular integral.**
Continuity (`innerAngular_continuous`) on the compact interval `[a, b]` gives
interval-integrability — exactly the shape of the `hInnerInt` hypothesis required by
`BuffonsNeedleOQ01OQ01.buffon_smooth_full`. -/
theorem innerAngular_intervalIntegrable (A B : ℝ → ℝ)
    (hA : Continuous A) (hB : Continuous B) (a b : ℝ) :
    IntervalIntegrable
      (fun t => ∫ θ in (0 : ℝ)..π, |A t * sin θ + B t * cos θ|) volume a b :=
  (innerAngular_continuous A B hA hB).intervalIntegrable a b

/-- Specialisation to a curve `γ`: the integrability hypothesis `hInnerInt` of
`buffon_smooth_full`, obtained from continuity of the two velocity components
`γ'₁ = deriv (Prod.fst ∘ γ)` and `γ'₂ = deriv (Prod.snd ∘ γ)`. -/
theorem hInnerInt_of_continuous_deriv (γ : ℝ → ℝ × ℝ) (a b : ℝ)
    (hA : Continuous (deriv (Prod.fst ∘ γ)))
    (hB : Continuous (deriv (Prod.snd ∘ γ))) :
    IntervalIntegrable
      (fun t => ∫ θ in (0 : ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ +
                                      (deriv (Prod.snd ∘ γ) t) * cos θ|) volume a b :=
  innerAngular_intervalIntegrable _ _ hA hB a b

/-- **Buffon–Barbier for a C¹ curve, with the integrability hypothesis removed.**

The expected number of crossings of a smooth curve with a unit grid equals
`2·length / (π·d)`, assuming only that

* each coordinate is differentiable on `[a, b]` (`hdx`, `hdy` — the C¹ assumption), and
* each velocity component is continuous (`hA`, `hB`).

Compared with `BuffonsNeedleOQ01OQ01.buffon_smooth_full`, the explicit
integrability hypothesis `hInnerInt` is gone: it is now *derived* from continuity
of the velocity via `hInnerInt_of_continuous_deriv`. -/
theorem buffon_smooth_C1
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ) (hd : 0 < d) (hab : a ≤ b)
    (hdx : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.fst ∘ γ) (deriv (Prod.fst ∘ γ) t) t)
    (hdy : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.snd ∘ γ) (deriv (Prod.snd ∘ γ) t) t)
    (hA : Continuous (deriv (Prod.fst ∘ γ)))
    (hB : Continuous (deriv (Prod.snd ∘ γ))) :
    BuffonsNeedleOQ01OQ01.concreteSmoothExpectedCrossings γ a b d
      = 2 * BuffonsNeedleOQ01OQ01.planarArcLength γ a b / (π * d) :=
  BuffonsNeedleOQ01OQ01.buffon_smooth_full γ a b d hd hab hdx hdy
    (hInnerInt_of_continuous_deriv γ a b hA hB)

end BuffonsNeedleOQ01OQ01OQ05
