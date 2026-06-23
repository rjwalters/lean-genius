/-
  Arc-length infrastructure and mean subtraction for regular closed curves
  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

  ## Context

  The parent entry `AreaOfCircleOQ01OQ02OQ02OQ01.lean` (`namespace
  IsoperimetricFromFourier`) proves the isoperimetric inequality `C² ≥ 4πA` from five
  disclosed axioms, the central one being `exists_nice_reparam`: every smooth closed curve
  can be reparametrized to **constant speed and zero mean** while keeping its circumference
  and area. The open question asks to discharge that axiom "from the inverse function
  theorem in Mathlib".

  Two prior survey sessions established the route and its two genuine specification gaps:

  * **Gap 1 (regularity).** A general C¹ closed curve may have stationary points
    (`γ'(t) = 0`); the arc-length map is then not strictly monotone and the inverse function
    theorem gives no `C¹` inverse. So the axiom is *false as literally stated* for
    non-regular curves — a regularity hypothesis `∀ t, 0 < |γ'(t)|²` is genuinely required.
  * **Gap 2 (mean subtraction).** Besides constant-speed reparametrization, the axiom also
    demands the witness have **zero mean** (`∫ x = ∫ y = 0`).

  ## What this file proves (0 axioms, 0 sorries, self-contained)

  This file builds, over Mathlib only, the verified analytic infrastructure for the IFT
  arc-length program **for regular curves**, with the regularity field built into the
  structure (Gap 1 made explicit):

  1. `speed` is continuous and strictly positive; arc length `s(t) = ∫₀ᵗ |γ'|` is
     differentiable with `s'(t) = speed(t)` (fundamental theorem of calculus,
     `integral_hasDerivAt_right`), hence **strictly monotone and injective** — the object
     the inverse function theorem inverts.
  2. **Mean subtraction** (Gap 2): translating each coordinate by its period-average mean
     produces a curve that is again a regular closed curve, has **zero mean**, and has the
     **same circumference, area, and speed** (the derivative is unchanged, and the signed-
     area correction term integrates to zero because `∫ x' = ∫ y' = 0` over a period).

  These are exactly the two ends — the strictly-monotone differentiable arc-length map and
  the zero-mean centering — that bracket the inverse-function-theorem core of
  `exists_nice_reparam`.

  ## Note on the broken sibling and parent (integrity flag)

  The full IFT arc-length reparametrization (the change-of-variables middle that joins these
  two ends) was previously written, `0`-axiom, in the sibling file
  `AreaOfCircleOQ01OQ03OQ01.lean` (`ArcLengthReparam.exists_arclength_reparam'`). However, as
  of Mathlib v4.26.0 **both that sibling and the parent `AreaOfCircleOQ01OQ02OQ02OQ01.lean`
  fail to build** (≈40 errors: `Real.contDiff_cos`, `Filter.eventually_of_forall`,
  `HasFDerivAtFilter.congr` were removed/renamed). They are gallery entries marked
  "verified" that have silently bit-rotted (audits use a cheap grep check, not `lake build`).
  This file therefore deliberately depends on **Mathlib only**, importing neither, so that it
  compiles and so that the infrastructure here survives the rot. Repairing those two entries
  is a separate mechanic task (flagged in the research notes).

  ## Sorries: 0   Axioms: 0
-/
import Mathlib

open Real MeasureTheory intervalIntegral Topology

namespace RegularCurveArcLength

/-- A regular C¹ closed plane curve: `C¹`, `2π`-periodic, with nowhere-vanishing speed.
The `regular` field is the hypothesis the survey identified as necessary for the inverse
function theorem (Gap 1). -/
structure RegularClosedCurve where
  /-- x-coordinate -/
  x : ℝ → ℝ
  /-- y-coordinate -/
  y : ℝ → ℝ
  /-- `x` is `C¹` -/
  smooth_x : ContDiff ℝ 1 x
  /-- `y` is `C¹` -/
  smooth_y : ContDiff ℝ 1 y
  /-- `x` is `2π`-periodic -/
  periodic_x : ∀ t, x (t + 2 * π) = x t
  /-- `y` is `2π`-periodic -/
  periodic_y : ∀ t, y (t + 2 * π) = y t
  /-- the curve is regular: its speed never vanishes -/
  regular : ∀ t, 0 < deriv x t ^ 2 + deriv y t ^ 2

namespace RegularClosedCurve

variable (γ : RegularClosedCurve)

/-- Speed `|γ'(t)| = √(x'² + y'²)`. -/
noncomputable def speed : ℝ → ℝ := fun t => Real.sqrt (deriv γ.x t ^ 2 + deriv γ.y t ^ 2)

/-- Circumference: arc length over one period. -/
noncomputable def circumference : ℝ := ∫ t in (0:ℝ)..(2 * π), speed γ t

/-- Enclosed signed area (Green's theorem). -/
noncomputable def area : ℝ :=
  (1 / 2) * |∫ t in (0:ℝ)..(2 * π), (γ.x t * deriv γ.y t - γ.y t * deriv γ.x t)|

/-- Arc length from `0` to `s`. -/
noncomputable def arcLength : ℝ → ℝ := fun s => ∫ t in (0:ℝ)..s, speed γ t

/-! ### Basic continuity and positivity -/

theorem continuous_x : Continuous γ.x := γ.smooth_x.continuous
theorem continuous_y : Continuous γ.y := γ.smooth_y.continuous
theorem continuous_deriv_x : Continuous (deriv γ.x) :=
  ((contDiff_succ_iff_deriv (n := 0)).mp γ.smooth_x).2.2.continuous
theorem continuous_deriv_y : Continuous (deriv γ.y) :=
  ((contDiff_succ_iff_deriv (n := 0)).mp γ.smooth_y).2.2.continuous

/-- The speed function is continuous. -/
theorem speed_continuous : Continuous (speed γ) := by
  unfold speed
  exact (((continuous_deriv_x γ).pow 2).add ((continuous_deriv_y γ).pow 2)).sqrt

/-- The speed function is strictly positive (regularity). -/
theorem speed_pos (t : ℝ) : 0 < speed γ t := by
  unfold speed
  exact Real.sqrt_pos.mpr (γ.regular t)

/-! ### The arc-length map: differentiable, strictly monotone, injective

This is the object the inverse function theorem inverts: a strictly monotone `C¹` map. -/

/-- Fundamental theorem of calculus: `s'(t) = speed(t)`. -/
theorem arcLength_hasDerivAt (s : ℝ) : HasDerivAt (arcLength γ) (speed γ s) s :=
  integral_hasDerivAt_right
    ((speed_continuous γ).intervalIntegrable 0 s)
    ((speed_continuous γ).stronglyMeasurableAtFilter volume (𝓝 s))
    (speed_continuous γ).continuousAt

/-- Consequently `deriv (arcLength γ) = speed γ`. -/
theorem deriv_arcLength (s : ℝ) : deriv (arcLength γ) s = speed γ s :=
  (arcLength_hasDerivAt γ s).deriv

/-- The arc-length map is strictly monotone (positive derivative everywhere). -/
theorem arcLength_strictMono : StrictMono (arcLength γ) :=
  strictMono_of_deriv_pos fun s => by rw [deriv_arcLength]; exact speed_pos γ s

/-- The arc-length map is injective. -/
theorem arcLength_injective : Function.Injective (arcLength γ) :=
  (arcLength_strictMono γ).injective

/-- The arc-length map is continuous (it is differentiable). -/
theorem arcLength_continuous : Continuous (arcLength γ) :=
  continuous_iff_continuousAt.mpr fun s => (arcLength_hasDerivAt γ s).continuousAt

/-! ### Mean subtraction (Gap 2): zero-mean centering

Centering preserves the derivative pointwise, hence circumference, area, and speed, while
forcing zero mean. Crucially the centered curve is *again regular*, so the centering can be
applied to the constant-speed reparametrization. -/

/-- The mean of `x` over one period. -/
noncomputable def meanX : ℝ := (∫ t in (0:ℝ)..(2 * π), γ.x t) / (2 * π)
/-- The mean of `y` over one period. -/
noncomputable def meanY : ℝ := (∫ t in (0:ℝ)..(2 * π), γ.y t) / (2 * π)

/-- The centered curve: each coordinate has its period-mean subtracted. It is again a regular
closed curve (subtracting a constant changes neither the derivative nor periodicity). -/
noncomputable def centered : RegularClosedCurve where
  x := fun t => γ.x t - meanX γ
  y := fun t => γ.y t - meanY γ
  smooth_x := γ.smooth_x.sub contDiff_const
  smooth_y := γ.smooth_y.sub contDiff_const
  periodic_x := fun t => by simp only [γ.periodic_x t]
  periodic_y := fun t => by simp only [γ.periodic_y t]
  regular := fun t => by simp only [deriv_sub_const]; exact γ.regular t

@[simp] theorem centered_x (t : ℝ) : (centered γ).x t = γ.x t - meanX γ := rfl
@[simp] theorem centered_y (t : ℝ) : (centered γ).y t = γ.y t - meanY γ := rfl

@[simp] theorem deriv_centered_x (t : ℝ) : deriv (centered γ).x t = deriv γ.x t := by
  show deriv (fun t => γ.x t - meanX γ) t = deriv γ.x t
  exact deriv_sub_const _
@[simp] theorem deriv_centered_y (t : ℝ) : deriv (centered γ).y t = deriv γ.y t := by
  show deriv (fun t => γ.y t - meanY γ) t = deriv γ.y t
  exact deriv_sub_const _

/-- The centered curve has the same speed. -/
@[simp] theorem speed_centered (t : ℝ) : speed (centered γ) t = speed γ t := by
  unfold speed
  rw [deriv_centered_x, deriv_centered_y]

/-- `meanX` times one period equals the integral of `x`. -/
theorem meanX_mul_period : meanX γ * (2 * π) = ∫ t in (0:ℝ)..(2 * π), γ.x t := by
  rw [meanX, div_mul_cancel₀ _ (by positivity : (2 : ℝ) * π ≠ 0)]
/-- `meanY` times one period equals the integral of `y`. -/
theorem meanY_mul_period : meanY γ * (2 * π) = ∫ t in (0:ℝ)..(2 * π), γ.y t := by
  rw [meanY, div_mul_cancel₀ _ (by positivity : (2 : ℝ) * π ≠ 0)]

/-- The integral of `x'` over a period vanishes (FTC plus periodicity). -/
theorem integral_deriv_x_eq_zero : (∫ t in (0:ℝ)..(2 * π), deriv γ.x t) = 0 := by
  have hsub : (∫ t in (0:ℝ)..(2 * π), deriv γ.x t) = γ.x (2 * π) - γ.x 0 := by
    apply intervalIntegral.integral_deriv_eq_sub
    · intro t _
      exact (γ.smooth_x.differentiable le_rfl).differentiableAt
    · exact (continuous_deriv_x γ).intervalIntegrable _ _
  rw [hsub]
  have h := γ.periodic_x 0
  rw [zero_add] at h
  rw [h, sub_self]

/-- The integral of `y'` over a period vanishes. -/
theorem integral_deriv_y_eq_zero : (∫ t in (0:ℝ)..(2 * π), deriv γ.y t) = 0 := by
  have hsub : (∫ t in (0:ℝ)..(2 * π), deriv γ.y t) = γ.y (2 * π) - γ.y 0 := by
    apply intervalIntegral.integral_deriv_eq_sub
    · intro t _
      exact (γ.smooth_y.differentiable le_rfl).differentiableAt
    · exact (continuous_deriv_y γ).intervalIntegrable _ _
  rw [hsub]
  have h := γ.periodic_y 0
  rw [zero_add] at h
  rw [h, sub_self]

/-- Centering forces zero mean in `x`. -/
theorem integral_centered_x_eq_zero : (∫ t in (0:ℝ)..(2 * π), (centered γ).x t) = 0 := by
  have hx_int : IntervalIntegrable γ.x volume 0 (2 * π) :=
    (continuous_x γ).intervalIntegrable _ _
  simp only [centered_x]
  rw [intervalIntegral.integral_sub hx_int (intervalIntegrable_const),
    intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    mul_comm (2 * π) (meanX γ), meanX_mul_period, sub_self]

/-- Centering forces zero mean in `y`. -/
theorem integral_centered_y_eq_zero : (∫ t in (0:ℝ)..(2 * π), (centered γ).y t) = 0 := by
  have hy_int : IntervalIntegrable γ.y volume 0 (2 * π) :=
    (continuous_y γ).intervalIntegrable _ _
  simp only [centered_y]
  rw [intervalIntegral.integral_sub hy_int (intervalIntegrable_const),
    intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    mul_comm (2 * π) (meanY γ), meanY_mul_period, sub_self]

/-- Centering preserves circumference (the integrand `speed` is unchanged). -/
theorem centered_circumference : (centered γ).circumference = γ.circumference := by
  unfold circumference
  apply intervalIntegral.integral_congr
  intro t _
  exact speed_centered γ t

/-- Centering preserves the signed area: the correction term integrates to zero because
`∫ x' = ∫ y' = 0` over a period. -/
theorem centered_area : (centered γ).area = γ.area := by
  unfold area
  have hxc : Continuous γ.x := continuous_x γ
  have hyc : Continuous γ.y := continuous_y γ
  have hdxc : Continuous (deriv γ.x) := continuous_deriv_x γ
  have hdyc : Continuous (deriv γ.y) := continuous_deriv_y γ
  have key :
      (∫ t in (0:ℝ)..(2 * π),
          (centered γ).x t * deriv (centered γ).y t
            - (centered γ).y t * deriv (centered γ).x t)
        = ∫ t in (0:ℝ)..(2 * π), (γ.x t * deriv γ.y t - γ.y t * deriv γ.x t) := by
    have hpt : ∀ t,
        (centered γ).x t * deriv (centered γ).y t
            - (centered γ).y t * deriv (centered γ).x t
          = (γ.x t * deriv γ.y t - γ.y t * deriv γ.x t)
            - (meanX γ * deriv γ.y t - meanY γ * deriv γ.x t) := by
      intro t
      simp only [centered_x, centered_y, deriv_centered_x, deriv_centered_y]
      ring
    rw [intervalIntegral.integral_congr (g := fun t =>
        (γ.x t * deriv γ.y t - γ.y t * deriv γ.x t)
          - (meanX γ * deriv γ.y t - meanY γ * deriv γ.x t)) (fun t _ => hpt t)]
    have horig_int : IntervalIntegrable
        (fun t => γ.x t * deriv γ.y t - γ.y t * deriv γ.x t) volume 0 (2 * π) :=
      (((hxc.mul hdyc).sub (hyc.mul hdxc))).intervalIntegrable _ _
    have hcorr_int : IntervalIntegrable
        (fun t => meanX γ * deriv γ.y t - meanY γ * deriv γ.x t) volume 0 (2 * π) :=
      (((continuous_const.mul hdyc).sub (continuous_const.mul hdxc))).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub horig_int hcorr_int]
    have hcorr_zero :
        (∫ t in (0:ℝ)..(2 * π), (meanX γ * deriv γ.y t - meanY γ * deriv γ.x t)) = 0 := by
      have hay_int : IntervalIntegrable (fun t => meanX γ * deriv γ.y t) volume 0 (2 * π) :=
        (continuous_const.mul hdyc).intervalIntegrable _ _
      have hbx_int : IntervalIntegrable (fun t => meanY γ * deriv γ.x t) volume 0 (2 * π) :=
        (continuous_const.mul hdxc).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hay_int hbx_int,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_deriv_x_eq_zero, integral_deriv_y_eq_zero, mul_zero, mul_zero, sub_zero]
    rw [hcorr_zero, sub_zero]
  rw [key]

/-! ### Summary: the centering operation has all the properties needed for `exists_nice_reparam`

Given any regular closed curve `δ` of constant speed `L/(2π)` (which the inverse-function-
theorem arc-length reparametrization produces), `centered δ` is a regular closed curve with
the *same* circumference, area, and (constant) speed, and additionally **zero mean**. Thus the
only missing link between this file and a full `0`-axiom proof of `exists_nice_reparam` (for
regular curves) is the constant-speed reparametrization itself — which exists `0`-axiom in the
sibling `AreaOfCircleOQ01OQ03OQ01.lean`, currently bit-rotted (see header). -/
theorem centered_preserves_all (hspeed : ∀ t, deriv γ.x t ^ 2 + deriv γ.y t ^ 2 = (γ.circumference / (2 * π)) ^ 2) :
    (centered γ).circumference = γ.circumference ∧
    (centered γ).area = γ.area ∧
    (∀ t, deriv (centered γ).x t ^ 2 + deriv (centered γ).y t ^ 2
        = (γ.circumference / (2 * π)) ^ 2) ∧
    (∫ t in (0:ℝ)..(2 * π), (centered γ).x t = 0) ∧
    (∫ t in (0:ℝ)..(2 * π), (centered γ).y t = 0) :=
  ⟨centered_circumference γ, centered_area γ,
   fun t => by rw [deriv_centered_x, deriv_centered_y]; exact hspeed t,
   integral_centered_x_eq_zero γ, integral_centered_y_eq_zero γ⟩

end RegularClosedCurve

end RegularCurveArcLength
