/-
  Full IFT arc-length reparametrization for regular closed curves: discharging
  `exists_nice_reparam` (the central reparametrization axiom of the isoperimetric proof)
  for regular curves, 0-axiom.

  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

  ## Context

  The parent entry `AreaOfCircleOQ01OQ02OQ02OQ01.lean` (`namespace IsoperimetricFromFourier`)
  proves the isoperimetric inequality `C² ≥ 4πA` from five disclosed axioms; the central one
  is `exists_nice_reparam`: every smooth closed curve admits a **constant-speed, zero-mean**
  reparametrization with the same circumference and area. The open question asks to discharge
  that axiom "from the inverse function theorem in Mathlib".

  Three prior sessions established the route and its two genuine specification gaps and built
  the two *ends* of the program in a self-contained companion
  `AreaOfCircleOQ01OQ02OQ02OQ01OQ01Reparam.lean` (`namespace RegularCurveArcLength`):

  * **Gap 1 (regularity).** A general C¹ closed curve may have stationary points
    (`γ'(t) = 0`); the arc-length map is then not strictly monotone and the inverse function
    theorem gives no `C¹` inverse. The axiom is *false as literally stated* for non-regular
    curves, so a regularity hypothesis `∀ t, 0 < |γ'(t)|²` is genuinely required. The companion
    bakes it into the `RegularClosedCurve` structure.
  * **Gap 2 (mean subtraction).** Besides constant speed, the axiom demands zero mean. The
    companion supplies `centered` and `centered_preserves_all`: subtracting each coordinate's
    period mean preserves circumference, area, and speed while forcing zero mean.

  The companion proved the two ends — the strictly-monotone differentiable arc-length map and
  the zero-mean centering. **This file builds the missing middle**: the `C¹` inverse of the
  arc-length map (inverse function theorem) and the change-of-variables computation showing the
  resulting constant-speed reparametrization preserves circumference and area. Combining the
  middle with the companion's `centered` ends gives, 0-axiom, the full `exists_nice_reparam`
  conclusion **for regular curves**:

  `exists_nice_reparam_for_regular` — every regular closed curve with positive circumference
  admits a regular closed curve with the same circumference and area, constant speed
  `(L/2π)`, and zero mean.

  ## Why this does not remove the parent axiom

  The parent's `isoperimetric_inequality` is stated for *all* `SmoothClosedCurve`, and the
  axiom is genuinely false for non-regular curves (Gap 1). This file discharges the axiom on
  the regular locus, which is where the IFT route can possibly succeed; it is the honest,
  maximal target of "prove `exists_nice_reparam` from the inverse function theorem".

  The construction mirrors the (Mathlib-v4.26.0 bit-rotted) sibling
  `AreaOfCircleOQ01OQ03OQ01.lean`'s `exists_arclength_reparam'`, but is rewritten on the
  current Mathlib pin and on the `RegularClosedCurve` structure, where the baked-in regularity
  field makes the arc-length map globally strictly monotone (no per-call hypothesis threading).

  ## Sorries: 0   Axioms: 0
-/
import Mathlib
import Proofs.AreaOfCircleOQ01OQ02OQ02OQ01OQ01Reparam

open Real MeasureTheory intervalIntegral Topology Filter

namespace RegularCurveArcLength

namespace RegularClosedCurve

variable (γ : RegularClosedCurve)

/-! ### Speed: squared identity and periodicity of the derivative -/

/-- `speed γ t ^ 2 = x'(t)² + y'(t)²` (the radicand is nonnegative by regularity). -/
theorem speed_sq (t : ℝ) : speed γ t ^ 2 = deriv γ.x t ^ 2 + deriv γ.y t ^ 2 := by
  unfold speed
  exact Real.sq_sqrt (le_of_lt (γ.regular t))

/-- `x'` is `2π`-periodic (translating the argument does not change the derivative). -/
theorem deriv_x_periodic (t : ℝ) : deriv γ.x (t + 2 * π) = deriv γ.x t := by
  have h : (fun s => γ.x (s + 2 * π)) = γ.x := funext γ.periodic_x
  have key : deriv (fun s => γ.x (s + 2 * π)) t = deriv γ.x (t + 2 * π) :=
    deriv_comp_add_const γ.x (2 * π) t
  rw [h] at key
  exact key.symm

/-- `y'` is `2π`-periodic. -/
theorem deriv_y_periodic (t : ℝ) : deriv γ.y (t + 2 * π) = deriv γ.y t := by
  have h : (fun s => γ.y (s + 2 * π)) = γ.y := funext γ.periodic_y
  have key : deriv (fun s => γ.y (s + 2 * π)) t = deriv γ.y (t + 2 * π) :=
    deriv_comp_add_const γ.y (2 * π) t
  rw [h] at key
  exact key.symm

/-- The speed function is `2π`-periodic. -/
theorem speed_periodic (t : ℝ) : speed γ (t + 2 * π) = speed γ t := by
  unfold speed
  rw [deriv_x_periodic, deriv_y_periodic]

/-! ### Periodic integral shift (generic helper) -/

/-- For a `2π`-periodic `f`, the integral over `[t, t+2π]` equals the integral over `[0, 2π]`. -/
theorem periodic_integral_shift (f : ℝ → ℝ) (t : ℝ)
    (hper : Function.Periodic f (2 * π)) :
    ∫ x in t..t + 2 * π, f x = ∫ x in (0 : ℝ)..2 * π, f x := by
  have h := hper.intervalIntegral_add_eq t 0
  simpa using h

/-! ### Arc-length: values at periodic points and quasi-periodicity -/

/-- `s(0) = 0`. -/
theorem arcLength_zero : arcLength γ 0 = 0 := by
  unfold arcLength
  simp [intervalIntegral.integral_same]

/-- `s(2π) = L` (the circumference). -/
theorem arcLength_period : arcLength γ (2 * π) = γ.circumference := rfl

/-- **Quasi-periodicity**: `s(t + 2π) = s(t) + L`. -/
theorem arcLength_quasi_periodic (t : ℝ) :
    arcLength γ (t + 2 * π) = arcLength γ t + γ.circumference := by
  have hsplit : arcLength γ (t + 2 * π) = arcLength γ t + ∫ u in t..(t + 2 * π), speed γ u := by
    unfold arcLength
    rw [← integral_add_adjacent_intervals
      ((speed_continuous γ).intervalIntegrable 0 t)
      ((speed_continuous γ).intervalIntegrable t (t + 2 * π))]
  rw [hsplit]
  congr 1
  rw [periodic_integral_shift (speed γ) t (speed_periodic γ)]
  rfl

/-- `s(n·2π) = n·L`. -/
theorem arcLength_nat_multiple (n : ℕ) :
    arcLength γ (n * (2 * π)) = n * γ.circumference := by
  induction n with
  | zero => simp [arcLength_zero]
  | succ n ih =>
    push_cast
    rw [show (↑n + 1) * (2 * π) = ↑n * (2 * π) + 2 * π by ring]
    rw [arcLength_quasi_periodic, ih]
    ring

/-- `s(-n·2π) = -n·L`. -/
theorem arcLength_neg_nat_multiple (n : ℕ) :
    arcLength γ (-(n * (2 * π))) = -(n * γ.circumference) := by
  induction n with
  | zero => simp [arcLength_zero]
  | succ n ih =>
    push_cast
    rw [show -((↑n + 1) * (2 * π)) = (-(↑n * (2 * π)) - 2 * π) by ring]
    have hqp := arcLength_quasi_periodic γ (-(↑n * (2 * π)) - 2 * π)
    rw [show -(↑n * (2 * π)) - 2 * π + 2 * π = -(↑n * (2 * π)) by ring] at hqp
    rw [ih] at hqp
    linarith

/-! ### Surjectivity (IVT) and the bijective inverse -/

/-- **Surjectivity** of arc-length: for a regular curve with positive circumference, `s : ℝ → ℝ`
is onto. -/
theorem arcLength_surjective (hL : 0 < γ.circumference) :
    Function.Surjective (arcLength γ) := by
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt (|y| / γ.circumference)
  have hn_L : |y| < n * γ.circumference := (div_lt_iff₀ hL).mp hn
  have hlo : arcLength γ (-(↑n * (2 * π))) ≤ y := by
    rw [arcLength_neg_nat_multiple]
    linarith [neg_abs_le y]
  have hhi : y ≤ arcLength γ (↑n * (2 * π)) := by
    rw [arcLength_nat_multiple]
    linarith [le_abs_self y]
  have hcont : ContinuousOn (arcLength γ) (Set.uIcc (-(↑n * (2 * π))) (↑n * (2 * π))) :=
    (arcLength_continuous γ).continuousOn
  have hmem : y ∈ Set.uIcc (arcLength γ (-(↑n * (2 * π)))) (arcLength γ (↑n * (2 * π))) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩)
  obtain ⟨t, _, ht⟩ := intermediate_value_uIcc hcont hmem
  exact ⟨t, ht⟩

/-- **Bijectivity** of arc-length. -/
theorem arcLength_bijective (hL : 0 < γ.circumference) :
    Function.Bijective (arcLength γ) :=
  ⟨arcLength_injective γ, arcLength_surjective γ hL⟩

/-- The arc-length inverse `σ = s⁻¹`. -/
noncomputable def arcLengthInv (hL : 0 < γ.circumference) : ℝ → ℝ :=
  (Equiv.ofBijective (arcLength γ) (arcLength_bijective γ hL)).symm

theorem arcLengthInv_left (hL : 0 < γ.circumference) (t : ℝ) :
    arcLengthInv γ hL (arcLength γ t) = t := by
  unfold arcLengthInv
  exact (Equiv.ofBijective (arcLength γ) (arcLength_bijective γ hL)).symm_apply_apply t

theorem arcLengthInv_right (hL : 0 < γ.circumference) (y : ℝ) :
    arcLength γ (arcLengthInv γ hL y) = y := by
  unfold arcLengthInv
  exact (Equiv.ofBijective (arcLength γ) (arcLength_bijective γ hL)).apply_symm_apply y

/-- **Quasi-periodicity of the inverse**: `σ(y + L) = σ(y) + 2π`. -/
theorem arcLengthInv_quasi_periodic (hL : 0 < γ.circumference) (y : ℝ) :
    arcLengthInv γ hL (y + γ.circumference) = arcLengthInv γ hL y + 2 * π := by
  have h1 := arcLength_quasi_periodic γ (arcLengthInv γ hL y)
  rw [arcLengthInv_right] at h1
  have h2 := arcLengthInv_left γ hL (arcLengthInv γ hL y + 2 * π)
  rw [h1] at h2
  exact h2

/-! ### The inverse function theorem: `σ` is `C¹` with `σ'(y) = 1/speed(σ(y))` -/

/-- **IFT derivative**: `σ'(y) = 1/speed(σ(y))`. -/
theorem arcLengthInv_hasDerivAt (hL : 0 < γ.circumference) (y : ℝ) :
    HasDerivAt (arcLengthInv γ hL) (1 / speed γ (arcLengthInv γ hL y)) y := by
  set σ := arcLengthInv γ hL with hσ_def
  set t₀ := σ y with ht₀_def
  have hspeed_pos : 0 < speed γ t₀ := speed_pos γ t₀
  have hstrict : HasStrictDerivAt (arcLength γ) (speed γ t₀) t₀ :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (Eventually.of_forall (arcLength_hasDerivAt γ))
      (speed_continuous γ).continuousAt
  have hleft : ∀ᶠ x in 𝓝 t₀, σ (arcLength γ x) = x :=
    Eventually.of_forall (arcLengthInv_left γ hL)
  have hσ_strict : HasStrictDerivAt σ (speed γ t₀)⁻¹ (arcLength γ t₀) :=
    hstrict.to_local_left_inverse (ne_of_gt hspeed_pos) hleft
  have hAL : arcLength γ t₀ = y := by
    rw [ht₀_def]; exact arcLengthInv_right γ hL y
  rw [hAL] at hσ_strict
  rw [one_div]
  exact hσ_strict.hasDerivAt

/-- **`σ` is `C¹`**. -/
theorem arcLengthInv_contDiff (hL : 0 < γ.circumference) :
    ContDiff ℝ 1 (arcLengthInv γ hL) := by
  set σ := arcLengthInv γ hL with hσ_def
  have hσ_mono : StrictMono σ := by
    intro a b hab
    by_contra h
    push_neg at h
    have hle : arcLength γ (σ b) ≤ arcLength γ (σ a) :=
      (arcLength_strictMono γ).monotone h
    rw [arcLengthInv_right, arcLengthInv_right] at hle
    linarith
  have hσ_surj : Function.Surjective σ :=
    fun t => ⟨arcLength γ t, arcLengthInv_left γ hL t⟩
  have hσ_cont : Continuous σ :=
    hσ_mono.monotone.continuous_of_surjective hσ_surj
  rw [contDiff_one_iff_deriv]
  refine ⟨fun y => (arcLengthInv_hasDerivAt γ hL y).differentiableAt, ?_⟩
  have hderiv_eq : ∀ y, deriv σ y = 1 / speed γ (σ y) :=
    fun y => (arcLengthInv_hasDerivAt γ hL y).deriv
  have heq : deriv σ = fun y => (speed γ (σ y))⁻¹ := by
    funext y; rw [hderiv_eq y, one_div]
  rw [heq]
  exact Continuous.inv₀ ((speed_continuous γ).comp hσ_cont) fun y => (speed_pos γ (σ y)).ne'

/-! ### The constant-speed reparametrization map `τ(t) = σ(c·t)`, `c = L/(2π)` -/

/-- The reparametrization map `τ(t) = σ(c·t)` with `c = L/(2π)`. -/
noncomputable def reparamMap (hL : 0 < γ.circumference) : ℝ → ℝ :=
  fun t => arcLengthInv γ hL (γ.circumference / (2 * π) * t)

/-- `τ` has derivative `1/speed(τ(t)) · c` (chain rule + IFT). -/
theorem reparamMap_hasDerivAt (hL : 0 < γ.circumference) (t : ℝ) :
    HasDerivAt (reparamMap γ hL)
      (1 / speed γ (reparamMap γ hL t) * (γ.circumference / (2 * π))) t := by
  have hσ := arcLengthInv_hasDerivAt γ hL (γ.circumference / (2 * π) * t)
  have h := hσ.comp t ((hasDerivAt_id t).const_mul (γ.circumference / (2 * π)))
  simpa only [Function.comp_def, mul_one] using h

/-- `τ` is `C¹`. -/
theorem reparamMap_contDiff (hL : 0 < γ.circumference) : ContDiff ℝ 1 (reparamMap γ hL) := by
  have h : ContDiff ℝ 1 (arcLengthInv γ hL ∘ (fun t => γ.circumference / (2 * π) * t)) :=
    (arcLengthInv_contDiff γ hL).comp (contDiff_const.mul contDiff_id)
  exact h

/-- `τ` is continuous. -/
theorem reparamMap_continuous (hL : 0 < γ.circumference) : Continuous (reparamMap γ hL) :=
  (reparamMap_contDiff γ hL).continuous

/-- **Quasi-periodicity of `τ`**: `τ(t + 2π) = τ(t) + 2π`. -/
theorem reparamMap_quasiPeriodic (hL : 0 < γ.circumference) (t : ℝ) :
    reparamMap γ hL (t + 2 * π) = reparamMap γ hL t + 2 * π := by
  unfold reparamMap
  rw [show γ.circumference / (2 * π) * (t + 2 * π)
        = γ.circumference / (2 * π) * t + γ.circumference by
      rw [mul_add, div_mul_cancel₀ _ (by positivity : (2 : ℝ) * π ≠ 0)]]
  exact arcLengthInv_quasi_periodic γ hL (γ.circumference / (2 * π) * t)

/-- Chain rule for `γ.x ∘ τ`. -/
theorem reparam_x_hasDerivAt (hL : 0 < γ.circumference) (t : ℝ) :
    HasDerivAt (γ.x ∘ reparamMap γ hL)
      (deriv γ.x (reparamMap γ hL t) * (1 / speed γ (reparamMap γ hL t) * (γ.circumference / (2 * π)))) t := by
  have hx : HasDerivAt γ.x (deriv γ.x (reparamMap γ hL t)) (reparamMap γ hL t) :=
    (γ.smooth_x.differentiable le_rfl).differentiableAt.hasDerivAt
  exact hx.comp t (reparamMap_hasDerivAt γ hL t)

/-- Chain rule for `γ.y ∘ τ`. -/
theorem reparam_y_hasDerivAt (hL : 0 < γ.circumference) (t : ℝ) :
    HasDerivAt (γ.y ∘ reparamMap γ hL)
      (deriv γ.y (reparamMap γ hL t) * (1 / speed γ (reparamMap γ hL t) * (γ.circumference / (2 * π)))) t := by
  have hy : HasDerivAt γ.y (deriv γ.y (reparamMap γ hL t)) (reparamMap γ hL t) :=
    (γ.smooth_y.differentiable le_rfl).differentiableAt.hasDerivAt
  exact hy.comp t (reparamMap_hasDerivAt γ hL t)

/-- **Constant speed**: `|d/dt (γ ∘ τ)|² = c²`. -/
theorem reparam_speed_sq (hL : 0 < γ.circumference) (t : ℝ) :
    deriv (γ.x ∘ reparamMap γ hL) t ^ 2 + deriv (γ.y ∘ reparamMap γ hL) t ^ 2
      = (γ.circumference / (2 * π)) ^ 2 := by
  rw [(reparam_x_hasDerivAt γ hL t).deriv, (reparam_y_hasDerivAt γ hL t).deriv]
  have hsp_ne : speed γ (reparamMap γ hL t) ≠ 0 := (speed_pos γ _).ne'
  have hsq : speed γ (reparamMap γ hL t) ^ 2
      = deriv γ.x (reparamMap γ hL t) ^ 2 + deriv γ.y (reparamMap γ hL t) ^ 2 := speed_sq γ _
  have harith : (deriv γ.x (reparamMap γ hL t)
        * (1 / speed γ (reparamMap γ hL t) * (γ.circumference / (2 * π)))) ^ 2
      + (deriv γ.y (reparamMap γ hL t)
        * (1 / speed γ (reparamMap γ hL t) * (γ.circumference / (2 * π)))) ^ 2
      = (deriv γ.x (reparamMap γ hL t) ^ 2 + deriv γ.y (reparamMap γ hL t) ^ 2)
        * (1 / speed γ (reparamMap γ hL t) * (γ.circumference / (2 * π))) ^ 2 := by ring
  rw [harith, ← hsq]
  field_simp

/-! ### The reparametrized curve and preservation of circumference / area -/

/-- The constant-speed reparametrization `γ' = γ ∘ τ`, again a regular closed curve. -/
noncomputable def reparam (hL : 0 < γ.circumference) : RegularClosedCurve where
  x := γ.x ∘ reparamMap γ hL
  y := γ.y ∘ reparamMap γ hL
  smooth_x := γ.smooth_x.comp (reparamMap_contDiff γ hL)
  smooth_y := γ.smooth_y.comp (reparamMap_contDiff γ hL)
  periodic_x := fun t => by
    show (γ.x ∘ reparamMap γ hL) (t + 2 * π) = (γ.x ∘ reparamMap γ hL) t
    simp only [Function.comp_apply, reparamMap_quasiPeriodic]
    exact γ.periodic_x _
  periodic_y := fun t => by
    show (γ.y ∘ reparamMap γ hL) (t + 2 * π) = (γ.y ∘ reparamMap γ hL) t
    simp only [Function.comp_apply, reparamMap_quasiPeriodic]
    exact γ.periodic_y _
  regular := fun t => by
    show 0 < deriv (γ.x ∘ reparamMap γ hL) t ^ 2 + deriv (γ.y ∘ reparamMap γ hL) t ^ 2
    rw [reparam_speed_sq γ hL t]
    exact pow_pos (div_pos hL (by positivity)) 2

@[simp] theorem reparam_x_eq (hL : 0 < γ.circumference) :
    (reparam γ hL).x = γ.x ∘ reparamMap γ hL := rfl
@[simp] theorem reparam_y_eq (hL : 0 < γ.circumference) :
    (reparam γ hL).y = γ.y ∘ reparamMap γ hL := rfl

/-- The reparametrized curve has constant speed `c = L/(2π)`. -/
theorem reparam_speed (hL : 0 < γ.circumference) (t : ℝ) :
    speed (reparam γ hL) t = γ.circumference / (2 * π) := by
  unfold speed
  have hsq : deriv (reparam γ hL).x t ^ 2 + deriv (reparam γ hL).y t ^ 2
      = (γ.circumference / (2 * π)) ^ 2 := by
    simp only [reparam_x_eq, reparam_y_eq]
    exact reparam_speed_sq γ hL t
  rw [hsq]
  exact Real.sqrt_sq (le_of_lt (div_pos hL (by positivity)))

/-- **Constant speed clause** for the reparametrization. -/
theorem reparam_speed_sq_eq (hL : 0 < γ.circumference) (t : ℝ) :
    deriv (reparam γ hL).x t ^ 2 + deriv (reparam γ hL).y t ^ 2
      = (γ.circumference / (2 * π)) ^ 2 := by
  simp only [reparam_x_eq, reparam_y_eq]
  exact reparam_speed_sq γ hL t

/-- **Circumference is preserved**: the reparametrization has constant speed `c`, so its
circumference is `2π·c = L`. -/
theorem reparam_circumference (hL : 0 < γ.circumference) :
    (reparam γ hL).circumference = γ.circumference := by
  have hconst : (reparam γ hL).circumference = ∫ _t in (0 : ℝ)..(2 * π), γ.circumference / (2 * π) := by
    unfold RegularClosedCurve.circumference
    exact intervalIntegral.integral_congr (fun t _ => reparam_speed γ hL t)
  rw [hconst, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm,
    div_mul_cancel₀ _ (by positivity : (2 : ℝ) * π ≠ 0)]

/-- **Area is preserved**: change of variables `u = τ(t)` plus periodicity of the signed-area
integrand. -/
theorem reparam_area (hL : 0 < γ.circumference) :
    (reparam γ hL).area = γ.area := by
  unfold RegularClosedCurve.area
  congr 1
  -- strip the absolute value: `|X| = |Y|` reduces to the integral identity `X = Y`
  congr 1
  simp only [reparam_x_eq, reparam_y_eq]
  -- The signed-area integrand of the original curve.
  have hg_per : ∀ u, (fun u => γ.x u * deriv γ.y u - γ.y u * deriv γ.x u) (u + 2 * π)
      = (fun u => γ.x u * deriv γ.y u - γ.y u * deriv γ.x u) u := fun u => by
    simp only
    rw [γ.periodic_x u, γ.periodic_y u, deriv_x_periodic γ u, deriv_y_periodic γ u]
  have hg_cont : Continuous (fun u => γ.x u * deriv γ.y u - γ.y u * deriv γ.x u) :=
    ((continuous_x γ).mul (continuous_deriv_y γ)).sub ((continuous_y γ).mul (continuous_deriv_x γ))
  have hτ_cont : Continuous (reparamMap γ hL) := reparamMap_continuous γ hL
  -- Pointwise: the reparametrized integrand is `(areaIntegrand ∘ τ)·τ'`.
  have hlhs_eq : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * π),
      (γ.x ∘ reparamMap γ hL) t * deriv (γ.y ∘ reparamMap γ hL) t
          - (γ.y ∘ reparamMap γ hL) t * deriv (γ.x ∘ reparamMap γ hL) t
        = ((fun u => γ.x u * deriv γ.y u - γ.y u * deriv γ.x u) ∘ reparamMap γ hL) t
          * (1 / speed γ (reparamMap γ hL t) * (γ.circumference / (2 * π))) := by
    intro t _
    rw [(reparam_x_hasDerivAt γ hL t).deriv, (reparam_y_hasDerivAt γ hL t).deriv]
    simp only [Function.comp_apply]
    ring
  rw [intervalIntegral.integral_congr hlhs_eq]
  -- Change of variables.
  have hτ_hasDerivAt : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * π),
      HasDerivAt (reparamMap γ hL) (1 / speed γ (reparamMap γ hL t) * (γ.circumference / (2 * π))) t :=
    fun t _ => reparamMap_hasDerivAt γ hL t
  have hf'_cont : ContinuousOn
      (fun t => 1 / speed γ (reparamMap γ hL t) * (γ.circumference / (2 * π)))
      (Set.uIcc 0 (2 * π)) := by
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.div continuousOn_const
    · exact ((speed_continuous γ).comp hτ_cont).continuousOn
    · intro t _; exact (speed_pos γ (reparamMap γ hL t)).ne'
  rw [intervalIntegral.integral_comp_mul_deriv' hτ_hasDerivAt hf'_cont
      (hg_cont.continuousOn.mono (Set.subset_univ _))]
  -- `τ(2π) = τ(0) + 2π`, then periodicity collapses to `[0, 2π]`.
  have hτ2π : reparamMap γ hL (2 * π) = reparamMap γ hL 0 + 2 * π := by
    have h := reparamMap_quasiPeriodic γ hL 0
    rwa [zero_add] at h
  rw [hτ2π]
  exact periodic_integral_shift (fun u => γ.x u * deriv γ.y u - γ.y u * deriv γ.x u)
    (reparamMap γ hL 0) hg_per

/-! ### Main results -/

/-- **Constant-speed reparametrization** (the IFT middle): every regular closed curve with
positive circumference admits a regular closed curve with the same circumference and area and
constant speed `L/(2π)`. -/
theorem exists_constant_speed_reparam (hL : 0 < γ.circumference) :
    ∃ δ : RegularClosedCurve,
      δ.circumference = γ.circumference ∧
      δ.area = γ.area ∧
      (∀ t, deriv δ.x t ^ 2 + deriv δ.y t ^ 2 = (γ.circumference / (2 * π)) ^ 2) :=
  ⟨reparam γ hL, reparam_circumference γ hL, reparam_area γ hL, reparam_speed_sq_eq γ hL⟩

/-- **`exists_nice_reparam` for regular curves (0-axiom).**

Every regular closed curve `γ` with positive circumference admits a regular closed curve `ρ`
that is

* circumference-preserving (`ρ.circumference = γ.circumference`),
* area-preserving (`ρ.area = γ.area`),
* of constant speed `(L/2π)` (`|ρ'(t)|² = (L/2π)²` for all `t`), and
* of zero mean (`∫₀²π ρ.x = ∫₀²π ρ.y = 0`).

This is exactly the conclusion of the parent's `exists_nice_reparam` axiom, discharged on the
regular locus where the inverse-function-theorem route applies. The constant-speed
reparametrization is built here via the IFT (`reparam`); the zero-mean centering is supplied by
the companion file's `centered`/`centered_preserves_all`. -/
theorem exists_nice_reparam_for_regular (hL : 0 < γ.circumference) :
    ∃ ρ : RegularClosedCurve,
      ρ.circumference = γ.circumference ∧
      ρ.area = γ.area ∧
      (∀ t, deriv ρ.x t ^ 2 + deriv ρ.y t ^ 2 = (γ.circumference / (2 * π)) ^ 2) ∧
      (∫ t in (0 : ℝ)..(2 * π), ρ.x t = 0) ∧
      (∫ t in (0 : ℝ)..(2 * π), ρ.y t = 0) := by
  obtain ⟨δ, hδc, hδa, hδspeed⟩ := exists_constant_speed_reparam γ hL
  refine ⟨centered δ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [centered_circumference, hδc]
  · rw [centered_area, hδa]
  · intro t; rw [deriv_centered_x, deriv_centered_y]; exact hδspeed t
  · exact integral_centered_x_eq_zero δ
  · exact integral_centered_y_eq_zero δ

end RegularClosedCurve

end RegularCurveArcLength
