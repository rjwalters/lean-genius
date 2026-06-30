import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-
# Reparametrization invariance of arc length and signed area

## What this file proves

The parent entry `AreaOfCircleOQ01OQ02OQ02OQ01.lean` proves the isoperimetric
inequality `C² ≥ 4πA` from five disclosed axioms, the central one being
`exists_nice_reparam`: every smooth closed curve can be reparametrized to
constant speed *while keeping its circumference and area*.

The open question `area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01` asks to discharge
that axiom "from the inverse function theorem in Mathlib". Two prior survey
sessions identified that the genuinely hard, axiom-free *mathematical heart* of
that program is the statement that **arc length and signed area are
reparametrization-invariant**: if `φ` is a `C¹` increasing change of parameter
that commutes with the period (`φ(2π) = φ(0) + 2π`), then `γ ∘ φ` has the same
circumference and the same signed area as `γ`. Once these are available, the
"circumference / area preservation" clauses of `exists_nice_reparam` become
*theorems about a change of variables* rather than assumptions, removing the
circularity flagged in the survey (the axiom currently only requires the witness
to *share* `γ`'s invariants, not to *be* a reparametrization of `γ`).

This file proves those two invariance facts as standalone, `0`-axiom theorems,
operating directly on the coordinate functions. They are exactly the change-of-
variables lemmas the eventual axiom discharge needs, and they are verifiable in
isolation (no dependency on the parent's structure or its other axioms).

## Mathematical content

For coordinate functions `x, y : ℝ → ℝ` and a reparametrization `φ : ℝ → ℝ`:

* **Arc length** `∫₀²π √((x∘φ)'² + (y∘φ)'²) = ∫₀²π √(x'² + y'²)`.
  Chain rule gives `(x∘φ)'(t) = x'(φ t)·φ'(t)`; since `φ' ≥ 0` the speed factors
  as `φ'(t)·speed(φ t)`, change of variables turns the integral into
  `∫_{φ0}^{φ(2π)} speed`, and the period-commuting condition plus periodicity of
  the speed collapse it back to `∫₀²π speed`.

* **Signed area** `∫₀²π ((x∘φ)·(y∘φ)' - (y∘φ)·(x∘φ)') = ∫₀²π (x·y' - y·x')`.
  Same change of variables; here no sign hypothesis on `φ'` is even needed for the
  algebra (the `φ'` factors out linearly), only the period-commuting condition.

Key Mathlib inputs: `deriv_comp` (chain rule),
`intervalIntegral.integral_comp_mul_deriv` (substitution), and
`Function.Periodic.intervalIntegral_add_eq` (period-shift invariance of the
integral over one period).
-/

open Real intervalIntegral MeasureTheory
open scoped Real

namespace AreaReparamInvariance

/-- The speed integrand `√(x'² + y'²)` whose integral over one period is the
circumference. -/
noncomputable def speedFn (x y : ℝ → ℝ) : ℝ → ℝ :=
  fun u => Real.sqrt (deriv x u ^ 2 + deriv y u ^ 2)

/-- The Green's-theorem integrand `x·y' - y·x'` whose integral over one period is
twice the signed area. -/
noncomputable def areaFn (x y : ℝ → ℝ) : ℝ → ℝ :=
  fun u => x u * deriv y u - y u * deriv x u

/-! ## Periodicity of the derivative -/

/-- The derivative of a periodic function is periodic with the same period.
Uses only `deriv_comp_add_const` and the period identity — no differentiability
hypothesis is required. -/
theorem periodic_deriv {f : ℝ → ℝ} {T : ℝ} (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro t
  have hfun : (fun s => f (s + T)) = f := funext hf
  calc deriv f (t + T)
      = deriv (fun s => f (s + T)) t := (deriv_comp_add_const f T t).symm
    _ = deriv f t := by rw [hfun]

/-! ## Speed and area integrands are periodic -/

/-- `speedFn x y` is `2π`-periodic when the coordinates are. -/
theorem speedFn_periodic {x y : ℝ → ℝ}
    (hx : Function.Periodic x (2 * π)) (hy : Function.Periodic y (2 * π)) :
    Function.Periodic (speedFn x y) (2 * π) := by
  have hdx := periodic_deriv hx
  have hdy := periodic_deriv hy
  intro t
  simp only [speedFn]
  rw [hdx t, hdy t]

/-- `areaFn x y` is `2π`-periodic when the coordinates are. -/
theorem areaFn_periodic {x y : ℝ → ℝ}
    (hx : Function.Periodic x (2 * π)) (hy : Function.Periodic y (2 * π)) :
    Function.Periodic (areaFn x y) (2 * π) := by
  have hdx := periodic_deriv hx
  have hdy := periodic_deriv hy
  intro t
  simp only [areaFn]
  rw [hx t, hy t, hdx t, hdy t]

/-! ## Chain rule for the coordinate composition -/

/-- Chain rule: `(x ∘ φ)'(t) = x'(φ t)·φ'(t)` for `C¹` data. -/
theorem deriv_coord_comp {x φ : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hφ : ContDiff ℝ 1 φ)
    (t : ℝ) : deriv (x ∘ φ) t = deriv x (φ t) * deriv φ t :=
  deriv_comp t (hx.differentiable le_rfl).differentiableAt
    (hφ.differentiable le_rfl).differentiableAt

/-! ## Arc length is reparametrization invariant -/

/-- **Arc length invariance.** For `C¹` coordinates `x, y` and a `C¹` increasing
reparametrization `φ` that commutes with the period (`φ(2π) = φ(0) + 2π`), the
circumference of `γ ∘ φ` equals the circumference of `γ`. -/
theorem arclength_reparam_invariant {x y φ : ℝ → ℝ}
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (hφ : ContDiff ℝ 1 φ)
    (hmono : ∀ t, 0 ≤ deriv φ t)
    (hxper : Function.Periodic x (2 * π)) (hyper : Function.Periodic y (2 * π))
    (hshift : φ (2 * π) = φ 0 + 2 * π) :
    (∫ t in (0 : ℝ)..(2 * π), speedFn (x ∘ φ) (y ∘ φ) t)
      = ∫ t in (0 : ℝ)..(2 * π), speedFn x y t := by
  -- Step 1: pointwise factor the speed of `γ ∘ φ` as `(speedFn x y ∘ φ)·φ'`.
  have key : Set.EqOn (speedFn (x ∘ φ) (y ∘ φ))
      (fun t => (speedFn x y ∘ φ) t * deriv φ t) (Set.uIcc 0 (2 * π)) := by
    intro t _
    have hp : 0 ≤ deriv φ t := hmono t
    simp only [speedFn, Function.comp_apply]
    rw [deriv_coord_comp hx hφ t, deriv_coord_comp hy hφ t]
    have hfac : (deriv x (φ t) * deriv φ t) ^ 2 + (deriv y (φ t) * deriv φ t) ^ 2
        = deriv φ t ^ 2 * (deriv x (φ t) ^ 2 + deriv y (φ t) ^ 2) := by ring
    rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp]
    ring
  rw [intervalIntegral.integral_congr key]
  -- Step 2: change of variables `u = φ t`.
  have hspeedcont : Continuous (speedFn x y) := by
    unfold speedFn
    exact (((hx.continuous_deriv le_rfl).pow 2).add
      ((hy.continuous_deriv le_rfl).pow 2)).sqrt
  have hcv : (∫ t in (0 : ℝ)..(2 * π), (speedFn x y ∘ φ) t * deriv φ t)
      = ∫ u in (φ 0)..(φ (2 * π)), speedFn x y u := by
    apply integral_comp_mul_deriv
    · intro t _
      exact (hφ.differentiable le_rfl).differentiableAt.hasDerivAt
    · exact (hφ.continuous_deriv le_rfl).continuousOn
    · exact hspeedcont
  rw [hcv, hshift]
  -- Step 3: the integral over one period does not depend on the basepoint.
  have hper := speedFn_periodic hxper hyper
  have := hper.intervalIntegral_add_eq (φ 0) 0
  simpa using this

/-! ## Signed area is reparametrization invariant -/

/-- **Signed area invariance.** For `C¹` coordinates `x, y` and a `C¹`
reparametrization `φ` that commutes with the period (`φ(2π) = φ(0) + 2π`), the
Green's-theorem integral `∫ (x·y' - y·x')` of `γ ∘ φ` equals that of `γ`.

Note that, unlike arc length, no monotonicity (`φ' ≥ 0`) hypothesis is needed:
the `φ'` factor enters linearly, so the algebra goes through for any `C¹` `φ`. -/
theorem signed_area_reparam_invariant {x y φ : ℝ → ℝ}
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (hφ : ContDiff ℝ 1 φ)
    (hxper : Function.Periodic x (2 * π)) (hyper : Function.Periodic y (2 * π))
    (hshift : φ (2 * π) = φ 0 + 2 * π) :
    (∫ t in (0 : ℝ)..(2 * π), areaFn (x ∘ φ) (y ∘ φ) t)
      = ∫ t in (0 : ℝ)..(2 * π), areaFn x y t := by
  -- Step 1: pointwise factor the integrand of `γ ∘ φ` as `(areaFn x y ∘ φ)·φ'`.
  have key : Set.EqOn (areaFn (x ∘ φ) (y ∘ φ))
      (fun t => (areaFn x y ∘ φ) t * deriv φ t) (Set.uIcc 0 (2 * π)) := by
    intro t _
    simp only [areaFn, Function.comp_apply]
    rw [deriv_coord_comp hy hφ t, deriv_coord_comp hx hφ t]
    ring
  rw [intervalIntegral.integral_congr key]
  -- Step 2: change of variables `u = φ t`.
  have hareacont : Continuous (areaFn x y) := by
    unfold areaFn
    exact (hx.continuous.mul (hy.continuous_deriv le_rfl)).sub
      (hy.continuous.mul (hx.continuous_deriv le_rfl))
  have hcv : (∫ t in (0 : ℝ)..(2 * π), (areaFn x y ∘ φ) t * deriv φ t)
      = ∫ u in (φ 0)..(φ (2 * π)), areaFn x y u := by
    apply integral_comp_mul_deriv
    · intro t _
      exact (hφ.differentiable le_rfl).differentiableAt.hasDerivAt
    · exact (hφ.continuous_deriv le_rfl).continuousOn
    · exact hareacont
  rw [hcv, hshift]
  -- Step 3: the integral over one period does not depend on the basepoint.
  have hper := areaFn_periodic hxper hyper
  have := hper.intervalIntegral_add_eq (φ 0) 0
  simpa using this

end AreaReparamInvariance
