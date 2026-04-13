import Mathlib

/-
# Archimedes' Method of Exhaustion: Connection to FTC Integration
# (area-of-circle-oq-01-oq-02-oq-03)

## The Open Question

**OQ-01-OQ-02-OQ-03**: Can Archimedes' classical exhaustion method be formally
connected to the modern FTC-based proof that A = ∫₀ʳ C(ρ) dρ?

## The Answer

Yes. Both methods compute the same quantity via different limiting processes:

**Method 1 (OQ-01-OQ-02, FTC)**: A(r) = ∫₀ʳ 2πρ dρ = πr²
  — uses the Fundamental Theorem of Calculus: A'(r) = C(r), then integrate.

**Method 2 (Archimedes)**: A(r) = lim_{n→∞} inscribedArea(n, r)
  — inscribed n-gon area = n/2 · r² · sin(2π/n) → πr² as n → ∞.

The key connection: both limits equal πr². By limit uniqueness in ℝ (Hausdorff),
there is a unique value toward which both the polygon approximations and the
FTC integral converge.

## What This File Proves (10 theorems, 0 sorries, 0 axioms)

**Part I**: FTC proof: ∫₀ʳ 2πρ dρ = πr²
**Part II**: Exhaustion proof: inscribedArea n r → πr²
**Part III**: Connection: both methods agree (uniqueness theorem)
-/

set_option linter.unusedVariables false

namespace AreaExhaustionFTC

open Real Filter Topology MeasureTheory intervalIntegral

noncomputable section

-- ============================================================
-- PART I: Circle Area via FTC
-- ============================================================

/-- The area of a circle: A(r) = πr². -/
def circleArea (r : ℝ) : ℝ := Real.pi * r ^ 2

/-- The circumference function: C(ρ) = 2πρ. -/
def circumference (ρ : ℝ) : ℝ := 2 * Real.pi * ρ

/-- The derivative of circleArea equals the circumference at each radius.
    A'(r) = 2πr = C(r). -/
theorem hasDerivAt_circleArea (r : ℝ) : HasDerivAt circleArea (circumference r) r := by
  unfold circleArea circumference
  have h : HasDerivAt (fun x => Real.pi * x ^ 2) (Real.pi * (2 * r)) r :=
    (hasDerivAt_pow 2 r).const_mul Real.pi |> (by simpa using ·)
  convert h using 1; ring

/-- **FTC Theorem**: ∫₀ʳ 2πρ dρ = πr²

    Proof: By FTC Part 2, since d/dρ[πρ²] = 2πρ = circumference(ρ). -/
theorem circumference_integral_eq (r : ℝ) :
    ∫ ρ in (0 : ℝ)..r, circumference ρ = circleArea r := by
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) r, HasDerivAt circleArea (circumference x) x :=
    fun x _ => hasDerivAt_circleArea x
  have h_int : IntervalIntegrable circumference volume 0 r :=
    (by unfold circumference; fun_prop : Continuous circumference).intervalIntegrable 0 r
  rw [integral_eq_sub_of_hasDerivAt h_deriv h_int]
  simp [circleArea]

-- ============================================================
-- PART II: Archimedes Inscribed Polygon
-- ============================================================

/-- The area of a regular n-gon inscribed in a circle of radius r.
    n isoceles triangles from center, each with area (1/2)r²sin(2π/n). -/
def inscribedArea (n : ℕ) (r : ℝ) : ℝ :=
  (n : ℝ) / 2 * r ^ 2 * Real.sin (2 * Real.pi / n)

/-- Helper: c / n → 0 as n → ∞, using tendsto_inv_atTop_zero. -/
private lemma tendsto_const_div_nat (c : ℝ) :
    Filter.Tendsto (fun n : ℕ => c / n) Filter.atTop (nhds 0) := by
  simp_rw [div_eq_mul_inv]
  have h_inv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := h_inv.const_mul c
  simp only [mul_zero] at h
  exact h

/-- sin(h)/h → 1 as h → 0 through nonzero values. -/
lemma tendsto_sin_div_nhds_zero :
    Filter.Tendsto (fun h : ℝ => Real.sin h / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have hd : HasDerivAt Real.sin 1 0 := by
    have := Real.hasDerivAt_sin 0
    rw [Real.cos_zero] at this; exact this
  rw [hasDerivAt_iff_tendsto_slope] at hd
  exact hd.congr' (Filter.Eventually.of_forall (fun y => by
    simp [slope_def_field, Real.sin_zero]))

/-- 2π/n → 0 through nonzero values as n → ∞. -/
lemma tendsto_two_pi_div_atTop :
    Filter.Tendsto (fun n : ℕ => (2 * Real.pi) / n)
      Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact tendsto_const_div_nat (2 * Real.pi)
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact Set.mem_compl_singleton_iff.mpr
      (div_ne_zero (by positivity) (Nat.cast_ne_zero.mpr (by omega)))

/-- n · sin(2π/n) → 2π as n → ∞. -/
private lemma tendsto_n_sin_two_pi_div_n :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.sin (2 * Real.pi / n))
      Filter.atTop (nhds (2 * Real.pi)) := by
  have key : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * Real.sin (2 * Real.pi / n) =
      2 * Real.pi * (Real.sin (2 * Real.pi / n) / (2 * Real.pi / n)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn']
  have h_comp : Filter.Tendsto
      (fun n : ℕ => Real.sin (2 * Real.pi / n) / (2 * Real.pi / n))
      Filter.atTop (nhds 1) :=
    tendsto_sin_div_nhds_zero.comp tendsto_two_pi_div_atTop
  have h_mul : Filter.Tendsto
      (fun n : ℕ => 2 * Real.pi * (Real.sin (2 * Real.pi / n) / (2 * Real.pi / n)))
      Filter.atTop (nhds (2 * Real.pi)) := by
    have := h_comp.const_mul (2 * Real.pi)
    simp only [mul_one] at this; exact this
  exact h_mul.congr' (key.mono (fun _ h => h.symm))

/-- **Archimedes**: inscribedArea n r → πr² as n → ∞. -/
theorem tendsto_inscribed_to_pi_r_sq (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => inscribedArea n r)
      Filter.atTop (nhds (Real.pi * r ^ 2)) := by
  unfold inscribedArea
  have h_lim : Filter.Tendsto
      (fun n : ℕ => r ^ 2 / 2 * ((n : ℝ) * Real.sin (2 * Real.pi / n)))
      Filter.atTop (nhds (r ^ 2 / 2 * (2 * Real.pi))) :=
    tendsto_const_nhds.mul tendsto_n_sin_two_pi_div_n
  have hgoal : Real.pi * r ^ 2 = r ^ 2 / 2 * (2 * Real.pi) := by ring
  rw [hgoal]
  apply h_lim.congr'
  filter_upwards with n; ring

-- ============================================================
-- PART III: The Exhaustion–FTC Connection
-- ============================================================

/-- **Main Connection**: The Archimedes exhaustion sequence converges
    to the same value as the FTC integral.

        lim_{n→∞} inscribedArea(n, r) = ∫₀ʳ 2πρ dρ = πr² -/
theorem exhaustion_equals_ftc (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => inscribedArea n r) Filter.atTop
      (nhds (∫ ρ in (0 : ℝ)..r, circumference ρ)) := by
  rw [circumference_integral_eq]
  simp only [circleArea]
  exact tendsto_inscribed_to_pi_r_sq r

/-- FTC and exhaustion define the same value. -/
theorem ftc_equals_exhaustion_limit (r : ℝ) :
    ∫ ρ in (0 : ℝ)..r, circumference ρ = circleArea r ∧
    Filter.Tendsto (fun n => inscribedArea n r) Filter.atTop (nhds (circleArea r)) :=
  ⟨circumference_integral_eq r, by
    simp only [circleArea]; exact tendsto_inscribed_to_pi_r_sq r⟩

/-- Inscribed n-gon area ≤ πr² for all n, r ≥ 0. -/
theorem inscribed_area_le_pi_r_sq (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    inscribedArea n r ≤ Real.pi * r ^ 2 := by
  unfold inscribedArea
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_div, zero_mul]; positivity
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have h_pos : 0 < 2 * Real.pi / n := by positivity
    have h_lt : Real.sin (2 * Real.pi / n) < 2 * Real.pi / n := Real.sin_lt h_pos
    have h_nonneg : 0 ≤ (n : ℝ) / 2 * r ^ 2 := by positivity
    calc (n : ℝ) / 2 * r ^ 2 * Real.sin (2 * Real.pi / n)
        ≤ (n : ℝ) / 2 * r ^ 2 * (2 * Real.pi / n) :=
          mul_le_mul_of_nonneg_left (le_of_lt h_lt) h_nonneg
      _ = Real.pi * r ^ 2 := by field_simp [ne_of_gt hn']

/-- Archimedes' squeeze from below. -/
theorem archimedes_squeeze_from_below (r : ℝ) (hr : 0 ≤ r) :
    ∀ n : ℕ, inscribedArea n r ≤ circleArea r := fun n => by
  simp only [circleArea]; exact inscribed_area_le_pi_r_sq n r hr

/-- ε-N form of Archimedes' exhaustion. -/
theorem archimedes_squeeze_approx (r : ℝ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |inscribedArea n r - circleArea r| < ε := by
  have hconv : Filter.Tendsto (fun n => inscribedArea n r) Filter.atTop (nhds (circleArea r)) :=
    by simp only [circleArea]; exact tendsto_inscribed_to_pi_r_sq r
  rw [Metric.tendsto_atTop] at hconv
  intro ε hε
  obtain ⟨N, hN⟩ := hconv ε hε
  exact ⟨N, fun n hn => by
    have h := hN n hn
    rw [Real.dist_eq] at h
    exact h⟩

/-- **Uniqueness**: Any limit of inscribed areas equals the FTC integral. -/
theorem two_methods_one_area (r : ℝ) (A : ℝ)
    (h_exhaust : Filter.Tendsto (fun n => inscribedArea n r) Filter.atTop (nhds A)) :
    A = ∫ ρ in (0 : ℝ)..r, circumference ρ :=
  tendsto_nhds_unique h_exhaust (exhaustion_equals_ftc r)

/-- Both methods prove the same formula: πr² = ∫₀ʳ 2πρ dρ. -/
theorem exhaustion_consistent (r : ℝ) :
    Real.pi * r ^ 2 = ∫ ρ in (0 : ℝ)..r, circumference ρ := by
  have h := circumference_integral_eq r
  simp only [circleArea] at h
  exact h.symm

end  -- close noncomputable section

end AreaExhaustionFTC
