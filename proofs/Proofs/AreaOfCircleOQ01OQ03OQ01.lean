/-
  Arc-Length Reparametrization for Smooth Closed Curves
  Open Question: area-of-circle-oq-01-oq-03-oq-01

  This file proves the arc-length reparametrization theorem for smooth closed curves,
  completing the analytic infrastructure underlying the isoperimetric inequality
  (AreaOfCircleOQ01OQ03.lean).

  The two remaining sorries in the parent proof are:
  1. The periodic integral shift: ∫_t^{t+2π} f = ∫_0^{2π} f for 2π-periodic f
     (needed for arclength_quasi_periodic)
  2. The arc-length reparametrization (exists_arclength_reparam)
     — which depends on: quasi-periodicity, surjectivity (IVT), C¹ inverse (IFT),
       and change-of-variables for integrals

  ## Key Results

  - **Periodic shift lemma** (PROVED): ∫_t^{t+T} f = ∫_0^T f for T-periodic integrable f
  - **Quasi-periodicity** (PROVED from shift lemma): s(t+2π) = s(t) + L
  - **Surjectivity via IVT** (PROVED): s is surjective from ℝ → ℝ
  - **C¹ inverse** (AXIOM): the IFT gives σ = s⁻¹ ∈ C¹
  - **IFT derivative** (AXIOM): σ'(y) = 1/speed(σ(y))
  - **Change of variables** (AXIOM): circumference and area preserved under σ
  - **Arc-length reparametrization** (PROVED from axioms): exists constant-speed curve
    with same circumference and area

  ## Sorries: 0
  ## Axioms: 4 (IFT for C¹ inverse, IFT derivative, two change-of-variables integrals)

  The 4 axioms correspond to:
  - The inverse function theorem for C¹ strictly monotone maps (missing from Mathlib for ℝ → ℝ)
  - Change-of-variables formula for interval integrals (available in Mathlib but technically
    complex to state for this composition)

  References:
  - do Carmo, Differential Geometry of Curves and Surfaces, §1-7
  - Hurwitz (1901): Fourier proof using arc-length reparametrization
  - AreaOfCircleOQ01OQ03.lean (parent proof)
-/

import Mathlib
import Proofs.AreaOfCircleOQ01OQ03

open Real Filter Topology MeasureTheory intervalIntegral

open IsoperimetricOQ

noncomputable section

namespace ArcLengthReparam

-- ============================================================
-- SECTION I: Periodic Functions and Integral Shift
-- ============================================================

/-- For a 2π-periodic continuous function f, the integral over any interval
    of length 2π equals ∫_0^{2π} f.

    **Proof**: Split ∫_t^{t+2π} = ∫_t^{2π} + ∫_{2π}^{t+2π}.
    For the second piece, substitute u = x + 2π:
      ∫_{2π}^{t+2π} f(u) du = ∫_0^t f(x+2π) dx = ∫_0^t f(x) dx.
    Then ∫_t^{2π} + ∫_0^t = ∫_0^{2π}. -/
theorem periodic_integral_shift (f : ℝ → ℝ) (t : ℝ)
    (hper : ∀ x, f (x + 2 * π) = f x)
    (hcont : Continuous f) :
    ∫ x in t..t + 2 * π, f x = ∫ x in (0 : ℝ)..2 * π, f x := by
  -- Step 1: Split ∫_t^{t+2π} at 2π
  rw [← integral_add_adjacent_intervals
    (hcont.intervalIntegrable t (2 * π))
    (hcont.intervalIntegrable (2 * π) (t + 2 * π))]
  -- Goal: ∫_t^{2π} f + ∫_{2π}^{t+2π} f = ∫_0^{2π} f
  -- Step 2: Rewrite ∫_{2π}^{t+2π} using periodicity substitution
  have hshift : ∫ x in (2 * π)..(t + 2 * π), f x = ∫ x in (0 : ℝ)..t, f x := by
    rw [← integral_comp_add_left f 0 t (2 * π)]
    -- Goal: ∫ x in 2π..t+2π, f x = ∫ x in 0..t, f(x+2π)
    simp only [zero_add]
    congr 1
    ext x
    exact (hper x).symm
  rw [hshift]
  -- Goal: ∫_t^{2π} f + ∫_0^t f = ∫_0^{2π} f
  -- Step 3: Combine via add_adjacent_intervals (reordering)
  rw [add_comm]
  exact integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 t)
    (hcont.intervalIntegrable t (2 * π))

-- ============================================================
-- SECTION II: Arc-Length Function Properties
-- ============================================================

/-- The speed function of a smooth closed curve: |γ'(t)| = √(x'(t)² + y'(t)²). -/
def curveSpeed (γ : SmoothClosedCurve) : ℝ → ℝ :=
  fun t => Real.sqrt (deriv γ.x t ^ 2 + deriv γ.y t ^ 2)

/-- The speed function is continuous. -/
theorem curveSpeed_continuous (γ : SmoothClosedCurve) : Continuous (curveSpeed γ) := by
  unfold curveSpeed
  apply Continuous.sqrt
  apply Continuous.add
  · apply Continuous.pow
    have h := (contDiff_succ_iff_deriv (n := 0)).mp γ.smooth_x
    exact h.2.2.continuous
  · apply Continuous.pow
    have h := (contDiff_succ_iff_deriv (n := 0)).mp γ.smooth_y
    exact h.2.2.continuous

/-- The speed function is 2π-periodic (since x and y are periodic). -/
theorem curveSpeed_periodic (γ : SmoothClosedCurve) (t : ℝ) :
    curveSpeed γ (t + 2 * π) = curveSpeed γ t := by
  unfold curveSpeed
  -- It suffices to show the expressions under sqrt are equal
  congr 1
  -- Prove deriv x (t + 2π) = deriv x t using HasDerivAt and periodicity
  have hxper : deriv γ.x (t + 2 * π) = deriv γ.x t := by
    have hd : ∀ s, HasDerivAt γ.x (deriv γ.x s) s :=
      fun s => (γ.smooth_x.differentiable le_rfl).differentiableAt.hasDerivAt
    have hd2 : HasDerivAt γ.x (deriv γ.x (t + 2 * π)) (t + 2 * π) := hd (t + 2 * π)
    have hd3 : HasDerivAt (fun s => γ.x (s + 2 * π)) (deriv γ.x (t + 2 * π)) t := by
      have := hd2.comp t ((hasDerivAt_id t).add (hasDerivAt_const t (2 * π)))
      simp only [mul_one, mul_zero, add_zero] at this
      exact this
    have := (hd t).congr (fun u => (γ.periodic_x u).symm) rfl
    rw [← hd3.deriv] at this
    exact this.symm
  have hyper : deriv γ.y (t + 2 * π) = deriv γ.y t := by
    have hd : ∀ s, HasDerivAt γ.y (deriv γ.y s) s :=
      fun s => (γ.smooth_y.differentiable le_rfl).differentiableAt.hasDerivAt
    have hd2 : HasDerivAt γ.y (deriv γ.y (t + 2 * π)) (t + 2 * π) := hd (t + 2 * π)
    have hd3 : HasDerivAt (fun s => γ.y (s + 2 * π)) (deriv γ.y (t + 2 * π)) t := by
      have := hd2.comp t ((hasDerivAt_id t).add (hasDerivAt_const t (2 * π)))
      simp only [mul_one, mul_zero, add_zero] at this
      exact this
    have := (hd t).congr (fun u => (γ.periodic_y u).symm) rfl
    rw [← hd3.deriv] at this
    exact this.symm
  rw [hxper, hyper]

/-- The arc-length function: s(t) = ∫_0^t |γ'(u)| du. -/
def arcLength (γ : SmoothClosedCurve) : ℝ → ℝ :=
  fun t => ∫ u in (0 : ℝ)..t, curveSpeed γ u

/-- The arc-length function has derivative equal to the speed at each point. -/
theorem arcLength_hasDerivAt (γ : SmoothClosedCurve) (t : ℝ) :
    HasDerivAt (arcLength γ) (curveSpeed γ t) t :=
  integral_hasDerivAt_right
    ((curveSpeed_continuous γ).intervalIntegrable 0 t)
    (curveSpeed_continuous γ).continuousAt

/-- The arc-length function is continuous. -/
theorem arcLength_continuous (γ : SmoothClosedCurve) :
    Continuous (arcLength γ) :=
  (fun t => (arcLength_hasDerivAt γ t).differentiableAt).continuous

/-- The arc-length function at 0 is 0. -/
theorem arcLength_zero (γ : SmoothClosedCurve) : arcLength γ 0 = 0 := by
  simp [arcLength, integral_same]

/-- The arc-length over [0, 2π] equals the circumference. -/
theorem arcLength_period (γ : SmoothClosedCurve) :
    arcLength γ (2 * π) = γ.circumference := by
  unfold arcLength SmoothClosedCurve.circumference curveSpeed
  rfl

/-- **Quasi-periodicity of arc-length** (PROVED from periodic_integral_shift):
    s(t + 2π) = s(t) + L.

    Proof: s(t+2π) = ∫_0^{t+2π} |γ'| = ∫_0^t |γ'| + ∫_t^{t+2π} |γ'|
    and ∫_t^{t+2π} |γ'| = ∫_0^{2π} |γ'| = L by the periodic shift lemma. -/
theorem arcLength_quasi_periodic (γ : SmoothClosedCurve) (t : ℝ) :
    arcLength γ (t + 2 * π) = arcLength γ t + γ.circumference := by
  unfold arcLength
  rw [integral_add_adjacent_intervals
    ((curveSpeed_continuous γ).intervalIntegrable 0 t)
    ((curveSpeed_continuous γ).intervalIntegrable t (t + 2 * π))]
  congr 1
  -- Prove ∫_t^{t+2π} speed = ∫_0^{2π} speed = circumference
  rw [periodic_integral_shift (curveSpeed γ) t (curveSpeed_periodic γ) (curveSpeed_continuous γ)]
  unfold SmoothClosedCurve.circumference curveSpeed

/-- Arc-length at integer multiples of 2π (positive). -/
theorem arcLength_nat_multiple (γ : SmoothClosedCurve) (n : ℕ) :
    arcLength γ (n * (2 * π)) = n * γ.circumference := by
  induction n with
  | zero => simp [arcLength_zero]
  | succ n ih =>
    push_cast
    rw [show (↑n + 1) * (2 * π) = ↑n * (2 * π) + 2 * π by ring]
    rw [arcLength_quasi_periodic, ih]
    ring

/-- Arc-length at negative multiples of 2π. -/
theorem arcLength_neg_nat_multiple (γ : SmoothClosedCurve) (n : ℕ) :
    arcLength γ (-(n * (2 * π))) = -(n * γ.circumference) := by
  induction n with
  | zero => simp [arcLength_zero]
  | succ n ih =>
    push_cast
    rw [show -((↑n + 1) * (2 * π)) = (-(↑n * (2 * π))) + (-2 * π) by ring]
    rw [show -(↑n * (2 * π)) + (-2 * π) = (-(↑n * (2 * π)) - 2 * π) from by ring]
    -- Use quasi-periodicity backwards: s(t - 2π) = s(t) - L
    -- From s(t + 2π) = s(t) + L, setting t → t - 2π: s(t) = s(t - 2π) + L
    -- So s(t - 2π) = s(t) - L
    have hqp := arcLength_quasi_periodic γ (-(↑n * (2 * π)) - 2 * π)
    rw [show -(↑n * (2 * π)) - 2 * π + 2 * π = -(↑n * (2 * π)) from by ring] at hqp
    rw [← ih] at hqp
    linarith

-- ============================================================
-- SECTION III: Surjectivity of Arc-Length via IVT
-- ============================================================

/-- **Surjectivity of arc-length** (PROVED via IVT):
    For any regular curve with positive circumference, the arc-length function
    s : ℝ → ℝ is surjective.

    Proof: For any y ∈ ℝ, find n : ℕ with n·L > |y|.
    Then s(2nπ) = nL > |y| ≥ y and s(-2nπ) = -nL < -|y| ≤ y.
    By IVT (s is continuous), ∃ t ∈ [-2nπ, 2nπ] with s(t) = y. -/
theorem arcLength_surjective (γ : SmoothClosedCurve)
    (hL : 0 < γ.circumference) :
    Function.Surjective (arcLength γ) := by
  intro y
  -- Find n : ℕ with n * L > |y|
  obtain ⟨n, hn⟩ := exists_nat_gt (|y| / γ.circumference)
  -- So n * L > |y|
  have hn_L : |y| < n * γ.circumference := by
    rwa [gt_iff_lt, lt_div_iff hL] at hn
  -- Lower bound: arcLength γ (-(n * 2π)) = -nL ≤ -|y| ≤ y
  have hlo : arcLength γ (-(↑n * (2 * π))) ≤ y := by
    rw [arcLength_neg_nat_multiple]
    push_neg
    linarith [neg_abs_le y]
  -- Upper bound: arcLength γ (n * 2π) = nL ≥ |y| ≥ y
  have hhi : y ≤ arcLength γ (↑n * (2 * π)) := by
    rw [arcLength_nat_multiple]
    push_cast
    linarith [le_abs_self y]
  -- Apply IVT: s is continuous on [-n·2π, n·2π], and hits both ≤ y and ≥ y
  have hcont : ContinuousOn (arcLength γ) (Set.uIcc (-(↑n * (2 * π))) (↑n * (2 * π))) :=
    (arcLength_continuous γ).continuousOn
  -- y is between s(lo) and s(hi), so IVT gives a preimage
  have hmem : y ∈ Set.uIcc (arcLength γ (-(↑n * (2 * π)))) (arcLength γ (↑n * (2 * π))) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩)
  obtain ⟨t, _, ht⟩ := intermediate_value_uIcc hcont hmem
  exact ⟨t, ht⟩

-- ============================================================
-- SECTION IV: C¹ Inverse via IFT (Axiomatized)
-- ============================================================

/-- **Strict monotonicity** of arc-length for regular curves.
    Proof: s'(t) = speed(t) > 0 everywhere for regular curves, so s is strictly increasing. -/
theorem arcLength_strictMono (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2) :
    StrictMono (arcLength γ) := by
  intro a b hab
  have hd_pos : ∀ x, 0 < deriv (arcLength γ) x := by
    intro x
    rw [(arcLength_hasDerivAt γ x).deriv]
    unfold curveSpeed
    exact Real.sqrt_pos.mpr (hReg x)
  have hcont : ContinuousOn (arcLength γ) (Set.Icc a b) :=
    (arcLength_continuous γ).continuousOn
  have hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt (arcLength γ) (deriv (arcLength γ) x) x :=
    fun x _ => (arcLength_hasDerivAt γ x).congr rfl rfl
  obtain ⟨c, _, hc_eq⟩ := exists_hasDerivAt_eq_slope (arcLength γ)
    (ne_of_lt hab) hcont (fun x hx => (hdiff x hx).hasDerivWithinAt)
  rw [div_eq_iff (sub_ne_zero.mpr (ne_of_lt hab))] at hc_eq
  linarith [hd_pos c, sub_pos.mpr hab]

/-- **Injectivity** of arc-length for regular curves. -/
theorem arcLength_injective (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2) :
    Function.Injective (arcLength γ) :=
  (arcLength_strictMono γ hReg).injective

/-- **Bijectivity** of arc-length for regular curves. -/
theorem arcLength_bijective (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) :
    Function.Bijective (arcLength γ) :=
  ⟨arcLength_injective γ hReg, arcLength_surjective γ hL⟩

/-- The inverse of the arc-length function (defined via bijectivity). -/
def arcLengthInv (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) : ℝ → ℝ :=
  (Equiv.ofBijective (arcLength γ) (arcLength_bijective γ hReg hL)).symm

/-- The inverse is a left inverse of arc-length. -/
theorem arcLengthInv_left (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) (t : ℝ) :
    arcLengthInv γ hReg hL (arcLength γ t) = t :=
  (Equiv.ofBijective _ _).symm_apply_apply t

/-- The inverse is a right inverse of arc-length. -/
theorem arcLengthInv_right (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) (y : ℝ) :
    arcLength γ (arcLengthInv γ hReg hL y) = y :=
  (Equiv.ofBijective _ _).apply_symm_apply y

/-- **Quasi-periodicity of the inverse**: σ(y + L) = σ(y) + 2π.
    Proof: From s(σ(y) + 2π) = s(σ(y)) + L = y + L by quasi-periodicity.
    Since s is injective, σ(y + L) = σ(y) + 2π. -/
theorem arcLengthInv_quasi_periodic (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) (y : ℝ) :
    arcLengthInv γ hReg hL (y + γ.circumference) =
    arcLengthInv γ hReg hL y + 2 * π := by
  have h1 := arcLength_quasi_periodic γ (arcLengthInv γ hReg hL y)
  rw [arcLengthInv_right] at h1
  have h2 := arcLengthInv_left γ hReg hL (arcLengthInv γ hReg hL y + 2 * π)
  rw [h1] at h2
  exact h2.symm

-- ============================================================
-- SECTION IV continued: C¹ Inverse via IFT (Proved)
-- ============================================================

/-- The derivative of the arc-length inverse at y is 1/speed(σ(y)).
    Proved via the Inverse Function Theorem:
    - arcLength has strict derivative speed(t) > 0 at t = σ(y) (from continuity of speed)
    - σ is a global left inverse of arcLength
    - IFT gives HasStrictDerivAt σ (speed(t))⁻¹ at arcLength(t) = y -/
theorem arcLengthInv_hasDerivAt (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) (y : ℝ) :
    HasDerivAt (arcLengthInv γ hReg hL)
      (1 / curveSpeed γ (arcLengthInv γ hReg hL y)) y := by
  set σ := arcLengthInv γ hReg hL with hσ_def
  set t₀ := σ y with ht₀_def
  -- Speed at t₀ is positive
  have hspeed_pos : 0 < curveSpeed γ t₀ := by
    unfold curveSpeed; exact Real.sqrt_pos.mpr (hReg t₀)
  -- arcLength has strict derivative speed(t₀) at t₀ (uses continuity of speed)
  have hstrict : HasStrictDerivAt (arcLength γ) (curveSpeed γ t₀) t₀ :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (Filter.eventually_of_forall (arcLength_hasDerivAt γ))
      (curveSpeed_continuous γ).continuousAt
  -- σ is a global (hence local) left inverse of arcLength
  have hleft : ∀ᶠ x in 𝓝 t₀, σ (arcLength γ x) = x :=
    Filter.eventually_of_forall (arcLengthInv_left γ hReg hL)
  -- IFT: σ has strict derivative (speed t₀)⁻¹ at arcLength t₀
  have hσ_strict : HasStrictDerivAt σ (curveSpeed γ t₀)⁻¹ (arcLength γ t₀) :=
    hstrict.to_local_left_inverse (ne_of_gt hspeed_pos) hleft
  -- arcLength t₀ = y (since t₀ = σ y = arcLengthInv y)
  have hAL : arcLength γ t₀ = y := by
    rw [ht₀_def]; exact arcLengthInv_right γ hReg hL y
  rw [hAL] at hσ_strict
  -- The goal: HasDerivAt σ (1/curveSpeed γ (σ y)) y
  -- σ y = t₀ and 1/speed(t₀) = (speed t₀)⁻¹
  rw [← ht₀_def, one_div]
  exact hσ_strict.hasDerivAt

/-- The inverse of the arc-length function is C¹.
    Proved using arcLengthInv_hasDerivAt: σ is differentiable everywhere with derivative
    1/speed(σ(y)), which is continuous (σ is continuous + speed is continuous + speed > 0). -/
theorem arcLengthInv_contDiff (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) :
    ContDiff ℝ 1 (arcLengthInv γ hReg hL) := by
  set σ := arcLengthInv γ hReg hL with hσ_def
  -- σ is strictly monotone (inverse of arcLength which is strictly monotone)
  have hσ_mono : StrictMono σ := by
    intro a b hab
    by_contra h
    push_neg at h
    have hle : arcLength γ (σ b) ≤ arcLength γ (σ a) :=
      (arcLength_strictMono γ hReg).monotone h
    rw [arcLengthInv_right, arcLengthInv_right] at hle
    linarith
  -- σ is surjective (it's the inverse of a bijection)
  have hσ_surj : Function.Surjective σ :=
    fun t => ⟨arcLength γ t, arcLengthInv_left γ hReg hL t⟩
  -- σ is continuous (monotone surjection on dense linear order)
  have hσ_cont : Continuous σ :=
    hσ_mono.monotone.continuous_of_surjective hσ_surj
  -- Use contDiff_one_iff_deriv: need differentiable + continuous deriv
  rw [contDiff_one_iff_deriv]
  constructor
  · -- Differentiable everywhere (from HasDerivAt)
    exact fun y => (arcLengthInv_hasDerivAt γ hReg hL y).differentiableAt
  · -- Continuous derivative: deriv σ y = 1/speed(σ y) is continuous
    have hderiv_eq : ∀ y, deriv σ y = 1 / curveSpeed γ (σ y) :=
      fun y => (arcLengthInv_hasDerivAt γ hReg hL y).deriv
    simp_rw [hderiv_eq, one_div]
    -- (curveSpeed γ (σ y))⁻¹ is continuous: σ continuous, speed continuous, speed > 0
    apply Continuous.inv₀ ((curveSpeed_continuous γ).comp hσ_cont)
    intro y
    exact (by unfold curveSpeed; exact Real.sqrt_pos.mpr (hReg (σ y))).ne'

-- ============================================================
-- SECTION V: Change of Variables for Integrals (Proved)
-- ============================================================

/-- Circumference is preserved under the reparametrization τ = σ ∘ (c · ·).
    The integrand sqrt((x∘τ)'² + (y∘τ)'²) equals c pointwise (by chain rule + IFT),
    so ∫_0^{2π} sqrt(...) dt = ∫_0^{2π} c dt = 2πc = L. -/
theorem circumference_reparam_preserved (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) :
    let c := γ.circumference / (2 * π)
    let σ := arcLengthInv γ hReg hL
    let τ := fun t => σ (c * t)
    ∫ t in (0 : ℝ)..(2 * π),
      Real.sqrt (deriv (γ.x ∘ τ) t ^ 2 + deriv (γ.y ∘ τ) t ^ 2) =
    γ.circumference := by
  intro c σ τ
  have hc_pos : 0 < c := div_pos hL (by positivity)
  have hcL : c * (2 * π) = γ.circumference := by
    field_simp [show (2 : ℝ) * π ≠ 0 from by positivity]
  -- τ has derivative (1/speed(τ t)) * c at each t (chain rule + IFT)
  have hτ_da : ∀ t, HasDerivAt τ (1 / curveSpeed γ (τ t) * c) t := fun t => by
    have hσ_da := arcLengthInv_hasDerivAt γ hReg hL (c * t)
    have h := hσ_da.comp t ((hasDerivAt_id t).const_mul c)
    simp only [Function.comp] at h
    convert h using 1; ring
  -- The integrand equals c pointwise (chain rule + algebraic simplification)
  have hint : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * π),
      Real.sqrt (deriv (γ.x ∘ τ) t ^ 2 + deriv (γ.y ∘ τ) t ^ 2) = c := by
    intro t _
    have hsp_pos : 0 < curveSpeed γ (τ t) := by
      unfold curveSpeed; exact Real.sqrt_pos.mpr (hReg (τ t))
    have hsp_ne : curveSpeed γ (τ t) ≠ 0 := hsp_pos.ne'
    have hk_pos : 0 ≤ 1 / curveSpeed γ (τ t) * c := by positivity
    -- Chain rule: deriv(x∘τ) t = deriv x (τ t) * deriv τ t
    have hx_da : HasDerivAt (γ.x ∘ τ) (deriv γ.x (τ t) * (1 / curveSpeed γ (τ t) * c)) t := by
      have hxt := (γ.smooth_x.differentiable le_rfl).differentiableAt.hasDerivAt (x := τ t)
      simpa [Function.comp] using hxt.comp t (hτ_da t)
    have hy_da : HasDerivAt (γ.y ∘ τ) (deriv γ.y (τ t) * (1 / curveSpeed γ (τ t) * c)) t := by
      have hyt := (γ.smooth_y.differentiable le_rfl).differentiableAt.hasDerivAt (x := τ t)
      simpa [Function.comp] using hyt.comp t (hτ_da t)
    rw [hx_da.deriv, hy_da.deriv]
    -- sqrt((x'·k)² + (y'·k)²) = speed(τt) · k = c
    rw [show (deriv γ.x (τ t) * (1 / curveSpeed γ (τ t) * c)) ^ 2 +
           (deriv γ.y (τ t) * (1 / curveSpeed γ (τ t) * c)) ^ 2 =
         (deriv γ.x (τ t) ^ 2 + deriv γ.y (τ t) ^ 2) * (1 / curveSpeed γ (τ t) * c) ^ 2 by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hk_pos]
    -- Now: sqrt(x'^2+y'^2) * (1/speed * c) = curveSpeed(τt) * (1/speed(τt) * c) = c
    show curveSpeed γ (τ t) * (1 / curveSpeed γ (τ t) * c) = c
    field_simp [hsp_ne]
  -- ∫_0^{2π} c dt = 2πc = L
  rw [intervalIntegral.integral_congr hint, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  linear_combination hcL

/-- Area is preserved under the reparametrization τ = σ ∘ (c · ·).
    Proved via change of variables and the periodic integral shift:
    ∫_0^{2π} [(x∘τ)(y∘τ)' - (y∘τ)(x∘τ)'] dt = ∫_{τ(0)}^{τ(2π)} [xy' - yx'] du
    and τ(2π) = τ(0) + 2π, so by periodicity this equals ∫_0^{2π} [xy' - yx'] dt. -/
theorem area_reparam_preserved (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) :
    let c := γ.circumference / (2 * π)
    let σ := arcLengthInv γ hReg hL
    let τ := fun t => σ (c * t)
    (1 / 2) * |∫ t in (0 : ℝ)..(2 * π),
      (γ.x ∘ τ) t * deriv (γ.y ∘ τ) t - (γ.y ∘ τ) t * deriv (γ.x ∘ τ) t| =
    (1 / 2) * |∫ t in (0 : ℝ)..(2 * π),
      γ.x t * deriv γ.y t - γ.y t * deriv γ.x t| := by
  intro c σ τ
  have hc_pos : 0 < c := div_pos hL (by positivity)
  have hcL : c * (2 * π) = γ.circumference := by
    field_simp [show (2 : ℝ) * π ≠ 0 from by positivity]
  -- τ derivative
  have hτ_da : ∀ t, HasDerivAt τ (1 / curveSpeed γ (τ t) * c) t := fun t => by
    have hσ_da := arcLengthInv_hasDerivAt γ hReg hL (c * t)
    have h := hσ_da.comp t ((hasDerivAt_id t).const_mul c)
    simp only [Function.comp] at h
    convert h using 1; ring
  have hτ'_pos : ∀ t, 0 < 1 / curveSpeed γ (τ t) * c := fun t => by
    apply mul_pos _ hc_pos
    apply div_pos one_pos
    unfold curveSpeed; exact Real.sqrt_pos.mpr (hReg (τ t))
  -- It suffices to show the integrals are equal (then the abs are equal)
  congr 1
  -- Define the area integrand g(u) = x(u)*y'(u) - y(u)*x'(u)
  -- Show that the LHS integrand = g(τ t) * τ'(t)
  have hlhs_eq : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * π),
      (γ.x ∘ τ) t * deriv (γ.y ∘ τ) t - (γ.y ∘ τ) t * deriv (γ.x ∘ τ) t =
      (γ.x (τ t) * deriv γ.y (τ t) - γ.y (τ t) * deriv γ.x (τ t)) *
        (1 / curveSpeed γ (τ t) * c) := by
    intro t _
    have hx_da : HasDerivAt (γ.x ∘ τ) (deriv γ.x (τ t) * (1 / curveSpeed γ (τ t) * c)) t := by
      have hxt := (γ.smooth_x.differentiable le_rfl).differentiableAt.hasDerivAt (x := τ t)
      simpa [Function.comp] using hxt.comp t (hτ_da t)
    have hy_da : HasDerivAt (γ.y ∘ τ) (deriv γ.y (τ t) * (1 / curveSpeed γ (τ t) * c)) t := by
      have hyt := (γ.smooth_y.differentiable le_rfl).differentiableAt.hasDerivAt (x := τ t)
      simpa [Function.comp] using hyt.comp t (hτ_da t)
    simp only [Function.comp]
    rw [hx_da.deriv, hy_da.deriv]
    ring
  -- Rewrite LHS integral using hlhs_eq
  have hLHS_eq : ∫ t in (0 : ℝ)..(2 * π),
      (γ.x ∘ τ) t * deriv (γ.y ∘ τ) t - (γ.y ∘ τ) t * deriv (γ.x ∘ τ) t =
    ∫ t in (0 : ℝ)..(2 * π),
      (fun u => γ.x u * deriv γ.y u - γ.y u * deriv γ.x u) (τ t) *
        (1 / curveSpeed γ (τ t) * c) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [Function.comp]
    exact hlhs_eq t ht
  rw [hLHS_eq]
  -- Apply change of variables: f = τ, g = area integrand, f' = 1/speed(τ t) * c
  have hτ_hasDerivAt : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * π),
      HasDerivAt τ (1 / curveSpeed γ (τ t) * c) t :=
    fun t _ => hτ_da t
  -- Continuity of τ' on [0, 2π]
  have hτ_cont : Continuous τ := by
    -- τ = σ ∘ (c * ·), σ continuous (from arcLengthInv_contDiff), (c*·) continuous
    have hσ_cont : Continuous σ := (arcLengthInv_contDiff γ hReg hL).continuous
    exact hσ_cont.comp (continuous_const.mul continuous_id)
  -- Area integrand continuity
  have hg_cont : Continuous (fun u => γ.x u * deriv γ.y u - γ.y u * deriv γ.x u) := by
    have hx_cont : Continuous γ.x := γ.smooth_x.continuous
    have hy_cont : Continuous γ.y := γ.smooth_y.continuous
    have hdx_cont : Continuous (deriv γ.x) := by
      have := (contDiff_succ_iff_deriv (n := 0)).mp γ.smooth_x; exact this.2.2.continuous
    have hdy_cont : Continuous (deriv γ.y) := by
      have := (contDiff_succ_iff_deriv (n := 0)).mp γ.smooth_y; exact this.2.2.continuous
    exact (hx_cont.mul hdy_cont).sub (hy_cont.mul hdx_cont)
  -- τ' continuity on [0, 2π]
  have hτ'_cont : ContinuousOn (fun t => 1 / curveSpeed γ (τ t) * c) (Set.uIcc 0 (2 * π)) := by
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.div continuousOn_const
    · exact ((curveSpeed_continuous γ).comp hτ_cont).continuousOn
    · intro t _
      exact (by unfold curveSpeed; exact Real.sqrt_pos.mpr (hReg (τ t))).ne'
  -- Apply change of variables: ∫_0^{2π} g(τ t) * τ'(t) dt = ∫_{τ(0)}^{τ(2π)} g u du
  rw [intervalIntegral.integral_comp_mul_deriv' hτ_hasDerivAt hτ'_cont
    (hg_cont.continuousOn.mono (Set.subset_univ _))]
  -- τ(0) and τ(2π)
  have hτ0 : τ 0 = σ 0 := by simp [τ, mul_zero]
  have hτ2π : τ (2 * π) = σ 0 + 2 * π := by
    simp only [τ]
    rw [show c * (2 * π) = γ.circumference from hcL]
    have := arcLengthInv_quasi_periodic γ hReg hL 0
    simp only [zero_add] at this
    exact this
  rw [hτ0, hτ2π]
  -- Area integrand is 2π-periodic
  have hg_per : ∀ u, γ.x (u + 2 * π) * deriv γ.y (u + 2 * π) -
      γ.y (u + 2 * π) * deriv γ.x (u + 2 * π) =
      γ.x u * deriv γ.y u - γ.y u * deriv γ.x u := fun u => by
    have hxper : γ.x (u + 2 * π) = γ.x u := γ.periodic_x u
    have hyper : γ.y (u + 2 * π) = γ.y u := γ.periodic_y u
    have hdxper : deriv γ.x (u + 2 * π) = deriv γ.x u := by
      have hd : ∀ s, HasDerivAt γ.x (deriv γ.x s) s :=
        fun s => (γ.smooth_x.differentiable le_rfl).differentiableAt.hasDerivAt
      have h1 := (hd u).congr (fun s => (γ.periodic_x s).symm) rfl
      have h3 : HasDerivAt (fun s => γ.x (s + 2 * π)) (deriv γ.x (u + 2 * π)) u := by
        have := (hd (u + 2 * π)).comp u
          ((hasDerivAt_id u).add (hasDerivAt_const u (2 * π)))
        simp only [mul_one, mul_zero, add_zero] at this; exact this
      rw [← h3.deriv] at h1; exact h1.symm
    have hdyper : deriv γ.y (u + 2 * π) = deriv γ.y u := by
      have hd : ∀ s, HasDerivAt γ.y (deriv γ.y s) s :=
        fun s => (γ.smooth_y.differentiable le_rfl).differentiableAt.hasDerivAt
      have h1 := (hd u).congr (fun s => (γ.periodic_y s).symm) rfl
      have h3 : HasDerivAt (fun s => γ.y (s + 2 * π)) (deriv γ.y (u + 2 * π)) u := by
        have := (hd (u + 2 * π)).comp u
          ((hasDerivAt_id u).add (hasDerivAt_const u (2 * π)))
        simp only [mul_one, mul_zero, add_zero] at this; exact this
      rw [← h3.deriv] at h1; exact h1.symm
    rw [hxper, hyper, hdxper, hdyper]
  -- Apply periodic shift: ∫_{σ(0)}^{σ(0)+2π} g = ∫_0^{2π} g
  exact periodic_integral_shift
    (fun u => γ.x u * deriv γ.y u - γ.y u * deriv γ.x u) (σ 0) hg_per hg_cont

-- ============================================================
-- SECTION VI: Main Theorem
-- ============================================================

/-- **Arc-Length Reparametrization Theorem** (PROVED from 4 axioms):

    Every regular smooth closed curve γ with positive circumference L admits a
    reparametrization γ' with:
    1. Same circumference: γ'.circumference = L
    2. Same area: γ'.area = A
    3. Constant speed: |γ'(t)|² = (L/2π)² for all t

    **Construction**: Let s = arc-length function, σ = s⁻¹ (C¹ by IFT),
    c = L/(2π), τ(t) = σ(c·t). Then γ'(t) = γ(τ(t)).

    **Speed of γ'**: By the chain rule,
      |γ'(t)|² = (x'(τ(t))·τ'(t))² + (y'(τ(t))·τ'(t))²
              = (x'(τ(t))² + y'(τ(t))²) · (τ'(t))²
              = speed(τ(t))² · (c/speed(τ(t)))²     [by IFT: σ'(ct) = 1/speed(σ(ct))]
              = c²

    **Periodicity of γ'**: τ(t+2π) = σ(c(t+2π)) = σ(ct + cL·(2π)) = σ(ct + L)
      = σ(ct) + 2π = τ(t) + 2π,  so γ'(t+2π) = γ(τ(t)+2π) = γ(τ(t)) = γ'(t). -/
theorem exists_arclength_reparam' (γ : SmoothClosedCurve)
    (hL : 0 < γ.circumference)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2) :
    ∃ γ' : SmoothClosedCurve,
      γ'.circumference = γ.circumference ∧
      γ'.area = γ.area ∧
      (∀ t, deriv γ'.x t ^ 2 + deriv γ'.y t ^ 2 = (γ.circumference / (2 * π)) ^ 2) := by
  -- Setup
  set L := γ.circumference with hL_def
  set c := L / (2 * π) with hc_def
  have hc_pos : 0 < c := div_pos hL (by positivity)
  have hcL : c * (2 * π) = L := by field_simp [show (2 : ℝ) * π ≠ 0 from by positivity]
  -- Arc-length inverse
  set σ := arcLengthInv γ hReg hL with hσ_def
  -- Reparametrization function τ(t) = σ(c·t)
  set τ : ℝ → ℝ := fun t => σ (c * t) with hτ_def
  -- τ is C¹ (composition of C¹ functions)
  have hτ_smooth : ContDiff ℝ 1 τ :=
    (arcLengthInv_contDiff γ hReg hL).comp (contDiff_const.mul contDiff_id)
  -- τ is 2π-periodic: τ(t+2π) = τ(t)
  -- Because σ(c(t+2π)) = σ(ct + cL·(2π)/L·... ) hmm let me use quasi-periodicity
  have hτ_periodic : ∀ t, τ (t + 2 * π) = τ t + 2 * π := by
    intro t
    simp only [hτ_def]
    rw [show c * (t + 2 * π) = c * t + L by rw [mul_add, hcL]]
    exact arcLengthInv_quasi_periodic γ hReg hL (c * t)
  -- Construct the reparametrized curve
  refine ⟨{
    x := γ.x ∘ τ
    y := γ.y ∘ τ
    periodic_x := fun t => by
      show γ.x (τ (t + 2 * π)) = γ.x (τ t)
      rw [hτ_periodic]; exact γ.periodic_x (τ t)
    periodic_y := fun t => by
      show γ.y (τ (t + 2 * π)) = γ.y (τ t)
      rw [hτ_periodic]; exact γ.periodic_y (τ t)
    smooth_x := γ.smooth_x.comp hτ_smooth
    smooth_y := γ.smooth_y.comp hτ_smooth
  }, ?_, ?_, ?_⟩
  -- Goal 1: Circumference preservation
  · exact circumference_reparam_preserved γ hReg hL
  -- Goal 2: Area preservation
  · exact area_reparam_preserved γ hReg hL
  -- Goal 3: Constant speed = c = L/(2π)
  · intro t
    show deriv (γ.x ∘ τ) t ^ 2 + deriv (γ.y ∘ τ) t ^ 2 = c ^ 2
    -- Speed at τ(t)
    have hsp_pos : 0 < curveSpeed γ (τ t) := by
      unfold curveSpeed; exact Real.sqrt_pos.mpr (hReg (τ t))
    have hsp_ne : curveSpeed γ (τ t) ≠ 0 := ne_of_gt hsp_pos
    have hsp_sq : curveSpeed γ (τ t) ^ 2 = deriv γ.x (τ t) ^ 2 + deriv γ.y (τ t) ^ 2 := by
      unfold curveSpeed
      exact Real.sq_sqrt (le_of_lt (hReg (τ t)))
    -- σ has derivative 1/speed(σ(ct)) at c*t (IFT axiom)
    have hσ_da : HasDerivAt σ (1 / curveSpeed γ (σ (c * t))) (c * t) :=
      arcLengthInv_hasDerivAt γ hReg hL (c * t)
    -- τ has derivative c/speed(τ(t)) at t
    have hτ_da : HasDerivAt τ (1 / curveSpeed γ (τ t) * c) t := by
      have := hσ_da.comp t ((hasDerivAt_id t).const_mul c)
      simp only [Function.comp, hτ_def] at this ⊢
      convert this using 1
      ring
    -- Chain rule for γ.x ∘ τ and γ.y ∘ τ
    have hx_da : HasDerivAt γ.x (deriv γ.x (τ t)) (τ t) :=
      (γ.smooth_x.differentiable le_rfl).differentiableAt.hasDerivAt
    have hy_da : HasDerivAt γ.y (deriv γ.y (τ t)) (τ t) :=
      (γ.smooth_y.differentiable le_rfl).differentiableAt.hasDerivAt
    rw [(hx_da.comp t hτ_da).deriv, (hy_da.comp t hτ_da).deriv]
    -- Arithmetic: (x'·c/s)² + (y'·c/s)² = (x'²+y'²)·c²/s² = c²
    have harith : (deriv γ.x (τ t) * (1 / curveSpeed γ (τ t) * c)) ^ 2 +
                  (deriv γ.y (τ t) * (1 / curveSpeed γ (τ t) * c)) ^ 2 =
                  (deriv γ.x (τ t) ^ 2 + deriv γ.y (τ t) ^ 2) *
                  (1 / curveSpeed γ (τ t) * c) ^ 2 := by ring
    rw [harith, ← hsp_sq, one_div, inv_pow, mul_pow,
      mul_comm (curveSpeed γ (τ t) ^ 2), mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hsp_ne), mul_one]

-- ============================================================
-- SECTION VII: Corollaries
-- ============================================================

/-- The circumference of the reparametrized curve equals the original. -/
theorem reparam_circumference_eq (γ : SmoothClosedCurve)
    (hL : 0 < γ.circumference)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2) :
    ∃ γ' : SmoothClosedCurve, γ'.circumference = γ.circumference :=
  let ⟨γ', h1, _, _⟩ := exists_arclength_reparam' γ hL hReg; ⟨γ', h1⟩

/-- The constant speed of the reparametrized curve is L/(2π). -/
theorem reparam_speed_is_L_over_2pi (γ : SmoothClosedCurve)
    (hL : 0 < γ.circumference)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2) :
    ∃ γ' : SmoothClosedCurve,
      ∀ t, Real.sqrt (deriv γ'.x t ^ 2 + deriv γ'.y t ^ 2) =
           γ.circumference / (2 * π) := by
  obtain ⟨γ', _, _, hspeed⟩ := exists_arclength_reparam' γ hL hReg
  exact ⟨γ', fun t => by
    have h := hspeed t
    rw [← Real.sqrt_sq (le_of_lt (div_pos hL (by positivity)))]
    rw [← h]
    exact Real.sqrt_sq_eq_abs _ |>.trans (abs_of_nonneg (Real.sqrt_nonneg _))⟩

/-- The arc-length function increases by L over each period of 2π. -/
theorem arcLength_grows_by_L (γ : SmoothClosedCurve) (t : ℝ) :
    arcLength γ (t + 2 * π) - arcLength γ t = γ.circumference :=
  by linarith [arcLength_quasi_periodic γ t]

/-- For regular curves, arc-length is a homeomorphism ℝ → ℝ (bijective + continuous). -/
theorem arcLength_bijection (γ : SmoothClosedCurve)
    (hReg : ∀ t, 0 < deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
    (hL : 0 < γ.circumference) :
    Function.Bijective (arcLength γ) ∧ Continuous (arcLength γ) :=
  ⟨arcLength_bijective γ hReg hL, arcLength_continuous γ⟩

end ArcLengthReparam

end
