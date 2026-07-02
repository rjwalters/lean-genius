import Mathlib
import Proofs.BuffonsNeedleOQ01OQ01

/-
# Discharging the Integrability Hypothesis for Buffon–Barbier (OQ-01-OQ-01-OQ-02)

## The Open Question

`BuffonsNeedleOQ01OQ01.lean` proves the Buffon–Barbier smooth-curve formula

  concreteSmoothExpectedCrossings γ a b d = 2 · planarArcLength γ a b / (π · d)

but its main theorems (`buffon_smooth_concrete`, `buffon_smooth_full`) carry an
explicit integrability hypothesis

  hInnerInt : IntervalIntegrable
    (fun t => ∫ θ in 0..π, |γ'ₓ(t) · sin θ + γ'ᵧ(t) · cos θ|) volume a b

on the *inner* angular integral, viewed as a function of the curve parameter `t`.
The open question (buffons-needle-oq-01-oq-01, listed openQuestion #2) asks:

  Can `hInnerInt` be **derived** from the smoothness of γ, rather than assumed?

## Answer: YES — it is a pointwise consequence of the angular-average theorem.

The whole difficulty evaporates once we observe that the *already-proved*
`angular_average` identity

  ∫ θ in 0..π, |a · sin θ + b · cos θ| = 2 · √(a² + b²)

holds for **every** pair `(a, b)`. Applying it pointwise at `(γ'ₓ(t), γ'ᵧ(t))`
shows the inner-integral function is *equal, as a function of `t`*, to

  t ↦ 2 · √(γ'ₓ(t)² + γ'ᵧ(t)²)   =   2 · ‖γ'(t)‖.

That is just twice the (continuous) speed of the curve. Hence:

* if the component derivatives are continuous, the inner-integral function is
  **continuous**, so a fortiori `IntervalIntegrable`;
* smoothness in the sense of `C¹` gives both the pointwise differentiability
  (`HasDerivAt`) needed by the parent theorem *and* the continuity of the
  derivatives, so the whole Buffon–Barbier formula holds for any `C¹` curve
  with **no** integrability side-condition.

## What This File Proves

- `innerIntegral_eq`        : the inner-integral function equals `2‖γ'(·)‖`.
- `innerIntegral_continuousOn` / `innerIntegral_continuous`
                            : continuity of the inner-integral function.
- `hInnerInt_of_continuousOn` / `hInnerInt_of_continuous`
                            : the integrability hypothesis, discharged.
- `buffon_smooth_of_continuousOn` / `buffon_smooth_of_continuous`
                            : Buffon–Barbier with `hInnerInt` removed.
- `buffon_smooth_of_contDiff`
                            : the headline — Buffon–Barbier for any `C¹` curve,
                              with *no* analytic side-conditions at all.

This closes the "integrability" gap in the parent formalization: the only genuine
analytic input remaining in the Buffon–Barbier chain is the angular-average
identity itself (already proved) — never a separate integrability assumption.
-/

namespace BuffonsNeedleOQ01OQ01OQ02

open Real intervalIntegral MeasureTheory
open BuffonsNeedleOQ01OQ01

/-!
## Part I: The inner-integral function is twice the speed

The inner angular integral, as a function of the curve parameter `t`, is
literally `2‖γ'(t)‖`.  This is a *pointwise* application of `angular_average`
and requires no hypotheses whatsoever.
-/

/-- The inner angular integral, as a function of the curve parameter `t`. -/
noncomputable def innerIntegral (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..π,
    |(deriv (Prod.fst ∘ γ) t) * sin θ + (deriv (Prod.snd ∘ γ) t) * cos θ|

/-- Twice the Euclidean speed `2‖γ'(t)‖` of the curve. -/
noncomputable def twiceSpeed (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  2 * Real.sqrt ((deriv (Prod.fst ∘ γ) t) ^ 2 + (deriv (Prod.snd ∘ γ) t) ^ 2)

/-- **Key reduction.** The inner-integral function is *equal*, everywhere, to
    `2‖γ'(·)‖`.  Immediate from the angular-average theorem applied pointwise. -/
theorem innerIntegral_eq (γ : ℝ → ℝ × ℝ) :
    innerIntegral γ = twiceSpeed γ := by
  funext t
  simpa [innerIntegral, twiceSpeed] using
    angular_average (deriv (Prod.fst ∘ γ) t) (deriv (Prod.snd ∘ γ) t)

/-!
## Part II: Continuity of the inner-integral function

Since `innerIntegral γ = 2‖γ'(·)‖`, continuity of the component derivatives
transfers directly.
-/

/-- If the component derivatives are continuous on `s`, so is the
    inner-integral function. -/
theorem innerIntegral_continuousOn (γ : ℝ → ℝ × ℝ) {s : Set ℝ}
    (hx : ContinuousOn (deriv (Prod.fst ∘ γ)) s)
    (hy : ContinuousOn (deriv (Prod.snd ∘ γ)) s) :
    ContinuousOn (innerIntegral γ) s := by
  rw [innerIntegral_eq]
  unfold twiceSpeed
  exact continuousOn_const.mul (((hx.pow 2).add (hy.pow 2)).sqrt)

/-- If the component derivatives are (globally) continuous, so is the
    inner-integral function. -/
theorem innerIntegral_continuous (γ : ℝ → ℝ × ℝ)
    (hx : Continuous (deriv (Prod.fst ∘ γ)))
    (hy : Continuous (deriv (Prod.snd ∘ γ))) :
    Continuous (innerIntegral γ) := by
  rw [innerIntegral_eq]
  unfold twiceSpeed
  exact continuous_const.mul (((hx.pow 2).add (hy.pow 2)).sqrt)

/-!
## Part III: The integrability hypothesis, discharged

`hInnerInt` of the parent file is exactly `IntervalIntegrable (innerIntegral γ)`.
Continuity gives interval-integrability immediately.
-/

/-- **The integrability hypothesis from continuity (local form).**
    Continuity of the derivatives on `uIcc a b` yields `hInnerInt`. -/
theorem hInnerInt_of_continuousOn (γ : ℝ → ℝ × ℝ) (a b : ℝ)
    (hx : ContinuousOn (deriv (Prod.fst ∘ γ)) (Set.uIcc a b))
    (hy : ContinuousOn (deriv (Prod.snd ∘ γ)) (Set.uIcc a b)) :
    IntervalIntegrable
      (fun t => ∫ θ in (0 : ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ +
                                      (deriv (Prod.snd ∘ γ) t) * cos θ|)
      volume a b :=
  (innerIntegral_continuousOn γ hx hy).intervalIntegrable

/-- **The integrability hypothesis from continuity (global form).** -/
theorem hInnerInt_of_continuous (γ : ℝ → ℝ × ℝ) (a b : ℝ)
    (hx : Continuous (deriv (Prod.fst ∘ γ)))
    (hy : Continuous (deriv (Prod.snd ∘ γ))) :
    IntervalIntegrable
      (fun t => ∫ θ in (0 : ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ +
                                      (deriv (Prod.snd ∘ γ) t) * cos θ|)
      volume a b :=
  (innerIntegral_continuous γ hx hy).intervalIntegrable a b

/-!
## Part IV: Buffon–Barbier without the integrability side-condition

Feeding the discharged hypothesis into `buffon_smooth_full` removes `hInnerInt`
from the statement entirely.
-/

/-- **Buffon–Barbier, integrability removed (continuity form).**  The concrete
    expected crossings equal `2L/(πd)` given only differentiability and
    *continuity* of the component derivatives on `uIcc a b`. -/
theorem buffon_smooth_of_continuousOn
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hdx : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.fst ∘ γ) (deriv (Prod.fst ∘ γ) t) t)
    (hdy : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.snd ∘ γ) (deriv (Prod.snd ∘ γ) t) t)
    (hcx : ContinuousOn (deriv (Prod.fst ∘ γ)) (Set.uIcc a b))
    (hcy : ContinuousOn (deriv (Prod.snd ∘ γ)) (Set.uIcc a b)) :
    concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) :=
  buffon_smooth_full γ a b d hd hab hdx hdy (hInnerInt_of_continuousOn γ a b hcx hcy)

/-- **Buffon–Barbier, integrability removed (global-continuity form).** -/
theorem buffon_smooth_of_continuous
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hdx : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.fst ∘ γ) (deriv (Prod.fst ∘ γ) t) t)
    (hdy : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.snd ∘ γ) (deriv (Prod.snd ∘ γ) t) t)
    (hcx : Continuous (deriv (Prod.fst ∘ γ)))
    (hcy : Continuous (deriv (Prod.snd ∘ γ))) :
    concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) :=
  buffon_smooth_full γ a b d hd hab hdx hdy (hInnerInt_of_continuous γ a b hcx hcy)

/-!
## Part V: The headline — Buffon–Barbier for any `C¹` curve

Smoothness in the sense of `C¹` supplies *both* ingredients the parent theorem
needs — pointwise differentiability (`HasDerivAt`) and continuity of the
derivatives — so no analytic side-condition survives.
-/

/-- **Buffon–Barbier for a `C¹` curve.**  If both coordinate functions of `γ`
    are continuously differentiable (`ContDiff ℝ 1`), then

      concreteSmoothExpectedCrossings γ a b d = 2 · planarArcLength γ a b / (π·d)

    with **no** integrability, Fubini, or differentiability side-conditions:
    they are all discharged from the single hypothesis that γ is `C¹`.  This is
    the natural analytic hypothesis of the classical Buffon–Barbier theorem. -/
theorem buffon_smooth_of_contDiff
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hx : ContDiff ℝ 1 (Prod.fst ∘ γ))
    (hy : ContDiff ℝ 1 (Prod.snd ∘ γ)) :
    concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) := by
  have hdx : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.fst ∘ γ) (deriv (Prod.fst ∘ γ) t) t :=
    fun t _ => (hx.differentiable le_rfl).differentiableAt.hasDerivAt
  have hdy : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.snd ∘ γ) (deriv (Prod.snd ∘ γ) t) t :=
    fun t _ => (hy.differentiable le_rfl).differentiableAt.hasDerivAt
  exact buffon_smooth_of_continuous γ a b d hd hab hdx hdy
    (hx.continuous_deriv le_rfl) (hy.continuous_deriv le_rfl)

end BuffonsNeedleOQ01OQ01OQ02
