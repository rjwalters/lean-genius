/-
  Convergence Rate of Inscribed Polygon Area
  Open Question: area-of-circle-oq-03-oq-01

  We prove that the area of a regular inscribed n-gon converges to πr²
  at rate O(1/n²). Specifically:

    0 ≤ πr² - Aₙ ≤ 2π³r²/(3n²)

  where Aₙ = inscribedArea(n, r) = n · r² / 2 · sin(2π/n).

  ## Mathematical Content

  The key inequality is sin(x) ≥ x - x³/6 for x ≥ 0, proved via a chain:
  1. sin(x) ≤ x for x ≥ 0  (Mathlib: Real.sin_lt)
  2. sin²(x) ≤ x² for x ≥ 0  (from step 1 + sign analysis)
  3. cos(x) ≥ 1 - x²/2 for x ≥ 0  (from half-angle identity + step 2)
  4. sin(x) ≥ x - x³/6 for x ≥ 0  (from MVT + step 3)

  Then the rate bound follows from algebra:
    πr² - Aₙ = r² · π · (1 - sin(u)/u)  where u = 2π/n
    ≤ r² · π · u²/6 = 2π³r²/(3n²)

  ## What This File Proves (0 sorries, 0 axioms)

  Trigonometric bounds:
  - sin_sq_le_sq: sin²(x) ≤ x² for x ≥ 0
  - cos_ge_one_sub_sq_div_two: cos(x) ≥ 1 - x²/2 for x ≥ 0
  - sin_ge_sub_cube_div_six: sin(x) ≥ x - x³/6 for x ≥ 0

  Convergence rate:
  - inscribed_area_upper: inscribedArea(n, r) ≤ πr² for r ≥ 0
  - inscribed_area_rate_bound: πr² - inscribedArea(n, r) ≤ 2π³r²/(3n²) for n ≥ 1
  - inscribed_area_convergence_rate: |inscribedArea(n, r) - πr²| ≤ 2π³r²/(3n²)
  - inscribed_area_error_positive: 0 < πr² - inscribedArea(n, r) for n ≥ 3, r > 0

  ## References
  - Classical approximation theory: Taylor remainder for trigonometric functions
  - Archimedes, "Measurement of a Circle" (c. 250 BCE)
-/

import Mathlib

namespace AreaOfCircleOQ03OQ01

open Real

noncomputable section

/-! ## Inscribed Polygon Area

The area of a regular n-gon inscribed in a circle of radius r is
n · r² / 2 · sin(2π/n), obtained by decomposing into n isoceles triangles. -/

/-- Area of a regular n-gon inscribed in a circle of radius r. -/
noncomputable def inscribedArea (n : ℕ) (r : ℝ) : ℝ :=
  n * r ^ 2 / 2 * Real.sin (2 * Real.pi / n)

/-! ## Step 1: sin²(x) ≤ x² for x ≥ 0 -/

/-- For x ≥ 0, sin(x)² ≤ x². -/
theorem sin_sq_le_sq {x : ℝ} (hx : 0 ≤ x) : Real.sin x ^ 2 ≤ x ^ 2 := by
  suffices h : 0 ≤ x ^ 2 - Real.sin x ^ 2 by linarith
  have : x ^ 2 - Real.sin x ^ 2 = (x - Real.sin x) * (x + Real.sin x) := by ring
  rw [this]
  apply mul_nonneg
  · rcases eq_or_lt_of_le hx with rfl | hpos
    · simp [Real.sin_zero]
    · linarith [Real.sin_lt hpos]
  · rcases le_or_gt 1 x with h1 | h1
    · have : -1 ≤ Real.sin x := neg_le_of_abs_le (abs_sin_le_one x)
      linarith
    · have : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_gt_three])
      linarith

/-! ## Step 2: cos(x) ≥ 1 - x²/2 for x ≥ 0 -/

/-- For x ≥ 0, cos(x) ≥ 1 - x²/2.

Uses the half-angle identity cos(x) = 1 - 2sin²(x/2) and sin²(x/2) ≤ (x/2)². -/
theorem cos_ge_one_sub_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 ≤ Real.cos x := by
  have hcos_eq : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (x / 2)
    rw [show 2 * (x / 2) = x from by ring] at h1
    have h2 := Real.sin_sq_add_cos_sq (x / 2)
    linarith
  rw [hcos_eq]
  have hx2 : (0 : ℝ) ≤ x / 2 := by linarith
  have h_sq := sin_sq_le_sq hx2
  nlinarith

/-! ## Step 3: sin(x) ≥ x - x³/6 for x ≥ 0

Uses the MVT on g(x) = sin(x) - x + x³/6, with g'(x) = cos(x) - 1 + x²/2 ≥ 0. -/

/-- The derivative of g(x) = sin(x) - x + x³/6 is cos(x) - 1 + x²/2. -/
theorem hasDerivAt_sin_sub_cube (x : ℝ) :
    HasDerivAt (fun t => Real.sin t - t + t ^ 3 / 6) (Real.cos x - 1 + x ^ 2 / 2) x := by
  have h1 : HasDerivAt (fun t => Real.sin t) (Real.cos x) x := Real.hasDerivAt_sin x
  have h2 : HasDerivAt (fun t => t) (1 : ℝ) x := hasDerivAt_id x
  have h3 : HasDerivAt (fun t => t ^ 3 / 6) (x ^ 2 / 2) x := by
    have h := (hasDerivAt_pow 3 x).div_const (6 : ℝ)
    convert h using 1
    simp; ring
  exact (h1.sub h2).add h3

/-- For x ≥ 0, sin(x) ≥ x - x³/6. The third-order Taylor lower bound for sin. -/
theorem sin_ge_sub_cube_div_six {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x := by
  suffices h : 0 ≤ Real.sin x - x + x ^ 3 / 6 by linarith
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp [Real.sin_zero]
  · set g : ℝ → ℝ := fun t => Real.sin t - t + t ^ 3 / 6 with hg_def
    set g' : ℝ → ℝ := fun t => Real.cos t - 1 + t ^ 2 / 2 with hg'_def
    have hg0 : g 0 = 0 := by simp [hg_def, Real.sin_zero]
    have hg_cont : ContinuousOn g (Set.Icc 0 x) := by
      apply ContinuousOn.add
      · exact (Real.continuous_sin.sub continuous_id).continuousOn
      · fun_prop
    have hg_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) x, HasDerivAt g (g' t) t :=
      fun t _ => hasDerivAt_sin_sub_cube t
    obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope g g' hx_pos hg_cont hg_deriv
    -- hc_eq : g'(c) = (g(x) - g(0)) / (x - 0)
    rw [hg0, sub_zero, sub_zero] at hc_eq
    -- hc_eq : g'(c) = g(x) / x, so g(x) = g'(c) * x
    have hc_nonneg : 0 ≤ c := le_of_lt hc.1
    have hg'_nonneg : 0 ≤ g' c := by
      rw [hg'_def]
      linarith [cos_ge_one_sub_sq_div_two hc_nonneg]
    have hgx : g x = g' c * x := by
      rwa [eq_comm, div_eq_iff (ne_of_gt hx_pos)] at hc_eq
    -- g(x) = g'(c) * x ≥ 0 since both factors are non-negative
    show 0 ≤ g x
    rw [hgx]
    exact mul_nonneg hg'_nonneg (le_of_lt hx_pos)

/-! ## Step 4: Inscribed Polygon Bounds -/

/-- The inscribed n-gon area is at most πr² for r ≥ 0.
Uses sin(x) < x for x > 0 from Mathlib. -/
theorem inscribed_area_upper (n : ℕ) (r : ℝ) (_hr : 0 ≤ r) :
    inscribedArea n r ≤ Real.pi * r ^ 2 := by
  unfold inscribedArea
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; nlinarith [Real.pi_pos, sq_nonneg r]
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have h_arg_pos : 0 < 2 * Real.pi / n := by positivity
    have h_sin_le : Real.sin (2 * Real.pi / n) ≤ 2 * Real.pi / n :=
      le_of_lt (Real.sin_lt h_arg_pos)
    -- n * r² / 2 * sin(2π/n) ≤ n * r² / 2 * (2π/n) = πr²
    have h1 : (n : ℝ) * r ^ 2 / 2 * Real.sin (2 * Real.pi / n) ≤
        (n : ℝ) * r ^ 2 / 2 * (2 * Real.pi / n) :=
      mul_le_mul_of_nonneg_left h_sin_le (by positivity)
    have h2 : (n : ℝ) * r ^ 2 / 2 * (2 * Real.pi / n) = Real.pi * r ^ 2 := by
      field_simp
    linarith

/-! ## Step 5: Convergence Rate -/

/-- Helper: u - sin(u) ≤ u³/6 for u ≥ 0. -/
theorem sub_sin_le_cube_div_six {u : ℝ} (hu : 0 ≤ u) :
    u - Real.sin u ≤ u ^ 3 / 6 := by
  linarith [sin_ge_sub_cube_div_six hu]

/-- **Main Theorem — Convergence Rate**:
The inscribed n-gon area converges to πr² at rate O(1/n²):

    πr² - inscribedArea(n, r) ≤ 2π³r²/(3n²)

Proof: sin(u) ≥ u - u³/6 gives n/2·sin(u) ≥ π - 2π³/(3n²),
hence πr² - inscribedArea ≤ 2π³r²/(3n²). -/
theorem inscribed_area_rate_bound (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (_hr : 0 ≤ r) :
    Real.pi * r ^ 2 - inscribedArea n r ≤
      2 * Real.pi ^ 3 * r ^ 2 / (3 * (n : ℝ) ^ 2) := by
  unfold inscribedArea
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  set u := 2 * Real.pi / (n : ℝ) with hu_def
  have hu_nonneg : 0 ≤ u := by positivity
  -- sin(u) ≥ u - u³/6
  have h_sin := sin_ge_sub_cube_div_six hu_nonneg
  -- n/2 · sin(u) ≥ n/2 · (u - u³/6)
  have h_mul : (n : ℝ) / 2 * Real.sin u ≥ (n : ℝ) / 2 * (u - u ^ 3 / 6) := by
    apply mul_le_mul_of_nonneg_left h_sin
    positivity
  -- n/2 · (u - u³/6) = π - 2π³/(3n²)  [algebra with u = 2π/n]
  have h_algebra : (n : ℝ) / 2 * (u - u ^ 3 / 6) =
      Real.pi - 2 * Real.pi ^ 3 / (3 * (n : ℝ) ^ 2) := by
    rw [hu_def]; field_simp; ring
  -- Therefore π - n/2·sin(u) ≤ 2π³/(3n²)
  have h_bound : Real.pi - (n : ℝ) / 2 * Real.sin u ≤
      2 * Real.pi ^ 3 / (3 * (n : ℝ) ^ 2) := by linarith
  -- Multiply by r² ≥ 0
  have herr : Real.pi * r ^ 2 - (↑n * r ^ 2 / 2 * Real.sin u) =
      r ^ 2 * (Real.pi - (n : ℝ) / 2 * Real.sin u) := by ring
  have htarget : 2 * Real.pi ^ 3 * r ^ 2 / (3 * (n : ℝ) ^ 2) =
      r ^ 2 * (2 * Real.pi ^ 3 / (3 * (n : ℝ) ^ 2)) := by ring
  rw [herr, htarget]
  exact mul_le_mul_of_nonneg_left h_bound (sq_nonneg r)

/-- **Convergence Rate (absolute value form)** -/
theorem inscribed_area_convergence_rate (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 ≤ r) :
    |inscribedArea n r - Real.pi * r ^ 2| ≤
      2 * Real.pi ^ 3 * r ^ 2 / (3 * (n : ℝ) ^ 2) := by
  rw [abs_le]
  constructor
  · have h := inscribed_area_rate_bound n hn r hr
    linarith
  · have h1 := inscribed_area_upper n r hr
    have h2 : 0 ≤ 2 * Real.pi ^ 3 * r ^ 2 / (3 * (n : ℝ) ^ 2) := by positivity
    linarith

/-- The error is strictly positive for n ≥ 3 and r > 0. -/
theorem inscribed_area_error_positive (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) :
    0 < Real.pi * r ^ 2 - inscribedArea n r := by
  unfold inscribedArea
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_pred (by omega)
  have h_pos : 0 < 2 * Real.pi / n := by positivity
  have h_sin_lt : Real.sin (2 * Real.pi / n) < 2 * Real.pi / n := Real.sin_lt h_pos
  have h_coeff_pos : 0 < (n : ℝ) * r ^ 2 / 2 := by positivity
  have h_lt : (n : ℝ) * r ^ 2 / 2 * Real.sin (2 * Real.pi / n) <
      (n : ℝ) * r ^ 2 / 2 * (2 * Real.pi / n) :=
    mul_lt_mul_of_pos_left h_sin_lt h_coeff_pos
  have h_eq : (n : ℝ) * r ^ 2 / 2 * (2 * Real.pi / n) = Real.pi * r ^ 2 := by
    field_simp
  linarith

end -- noncomputable section

end AreaOfCircleOQ03OQ01
