/-
  The full isoperimetric inequality `C² ≥ 4πA` for regular closed plane curves,
  assembled 0-axiom from the five analytic ingredients discharged in the sibling
  companion files.

  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

  ## Context

  The parent entry `AreaOfCircleOQ01OQ02OQ02OQ01.lean` (`namespace IsoperimetricFromFourier`)
  proves Hurwitz's 1901 isoperimetric inequality `C² ≥ 4πA` for smooth closed curves from
  **five disclosed axioms** isolating its analytic content:

    1. `fourier_decomp_exists`        — Parseval + IBP for periodic C¹ functions
    2. `exists_nice_reparam`          — arc-length reparametrization (inverse function theorem)
    3. `wirtinger_sum_bound`          — Wirtinger's inequality on the coordinate functions
    4. `area_cauchy_schwarz_bound`    — Green's theorem + pointwise 2D Cauchy–Schwarz
    5. `integral_cauchy_schwarz_sq`   — the L² Cauchy–Schwarz on `[0, 2π]`

  Prior sessions discharged **all five** 0-axiom, but each in an isolated standalone file:

    * `…OQ01OQ01IFT.lean`         — `RegularClosedCurve.exists_nice_reparam_for_regular`
                                    (axiom 2 on the regular locus, via the IFT)
    * `…OQ01OQ01Fourier.lean`    — `IsoperimetricFourier.wirtinger_sum_bound`
                                    (axioms 1 + 3, via Parseval)
    * `…OQ01OQ01CauchySchwarz.lean` — `IsoperimetricCauchySchwarz.area_cauchy_schwarz_bound_contDiff`
                                    and `integral_cauchy_schwarz_sq` (axioms 4 + 5)

  **This file is the capstone**: it wires those three discharged pieces together — through
  the same purely-algebraic arithmetic kernel the parent uses — to obtain the *complete*
  isoperimetric inequality with **zero axioms**:

  `isoperimetric_inequality_regular` — for every regular closed plane curve `γ` with positive
  circumference, `4π·area ≤ circumference²`.

  ## Honest scope

  The result is stated for `RegularClosedCurve` (C¹, 2π-periodic, nowhere-vanishing speed),
  not the parent's `SmoothClosedCurve`. This is the *maximal honest target*: the parent axiom
  `exists_nice_reparam` is genuinely **false** for non-regular curves — a curve with a
  stationary point (`γ'(t) = 0`) has a non-strictly-monotone arc-length map and the inverse
  function theorem gives no C¹ inverse (Gap 1, established in session s01 and unchanged since).
  So `C² ≥ 4πA` for *all* smooth closed curves cannot be obtained by this Fourier/IFT route
  without an additional limiting argument; on the regular locus, where the route is valid, this
  file delivers the inequality entirely axiom-free.

  Unlike the parent, this file imports **none** of the axiomatized infrastructure — only the
  three 0-axiom sibling companions (and `Mathlib`). The arithmetic kernel is reproved inline
  (the parent's copy lives in the bit-rotted parent file, which does not build on Mathlib
  v4.26.0).

  ## Sorries: 0   Axioms: 0
-/
import Mathlib
import Proofs.AreaOfCircleOQ01OQ02OQ02OQ01OQ01IFT
import Proofs.AreaOfCircleOQ01OQ02OQ02OQ01OQ01Fourier
import Proofs.AreaOfCircleOQ01OQ02OQ02OQ01OQ01CauchySchwarz

open Real MeasureTheory intervalIntegral

namespace IsoperimetricRegular

open RegularCurveArcLength

noncomputable section

/-! ### The arithmetic kernel (purely algebraic)

Given the four analytic bounds, the isoperimetric inequality is pure arithmetic:
`S² ≤ 2π·Sxy ≤ 2π·(2πc²) = (2πc)²`, so `S ≤ 2πc`; then `2A ≤ c·S ≤ 2πc²`, hence
`4πA ≤ 4π²c² = (2πc)² = L²`. No integrals or measures appear. (Reproved inline rather than
imported from the bit-rotted parent file.) -/
theorem isoperimetric_arithmetic_kernel
    (A L c S Sxy : ℝ)
    (hc : 0 < c)
    (hcirc : L = 2 * π * c)
    (hS_nn : 0 ≤ S)
    (harea : 2 * A ≤ c * S)
    (hCS : S ^ 2 ≤ 2 * π * Sxy)
    (hWirt : Sxy ≤ 2 * π * c ^ 2) :
    4 * π * A ≤ L ^ 2 := by
  have hpi : (0 : ℝ) < π := pi_pos
  have h2pic_pos : (0 : ℝ) < 2 * π * c := by positivity
  have hS2 : S ^ 2 ≤ (2 * π * c) ^ 2 :=
    calc S ^ 2 ≤ 2 * π * Sxy := hCS
      _ ≤ 2 * π * (2 * π * c ^ 2) := mul_le_mul_of_nonneg_left hWirt (by linarith)
      _ = (2 * π * c) ^ 2 := by ring
  have hS_bound : S ≤ 2 * π * c := by
    have h := Real.sqrt_le_sqrt hS2
    rwa [Real.sqrt_sq hS_nn, Real.sqrt_sq h2pic_pos.le] at h
  have h1 : c * S ≤ 2 * π * c ^ 2 := by nlinarith
  have h2 : 2 * A ≤ 2 * π * c ^ 2 := le_trans harea h1
  calc 4 * π * A = 2 * π * (2 * A) := by ring
    _ ≤ 2 * π * (2 * π * c ^ 2) := mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = (2 * π * c) ^ 2 := by ring
    _ = L ^ 2 := by rw [hcirc]

/-! ### The full isoperimetric inequality for regular closed curves -/

/-- **The Isoperimetric Inequality for regular closed curves** (Hurwitz 1901), 0-axiom.

For any regular closed plane curve `γ` (C¹, 2π-periodic, nowhere-vanishing speed) with positive
circumference `C` and signed area `A`,
  `4π·A ≤ C²`,
with equality for the circle.

Proof. Reparametrize `γ` to a constant-speed (`c = C/2π`), zero-mean regular closed curve `ρ`
with the same circumference and area (`exists_nice_reparam_for_regular`, the IFT discharge of
axiom 2). On `ρ`:
* Wirtinger (`wirtinger_sum_bound`, axioms 1+3) gives `∫(x²+y²) ≤ 2πc²`;
* Cauchy–Schwarz (`area_cauchy_schwarz_bound_contDiff`, axiom 4) gives `2A = |∫(x·y'−y·x')| ≤ c·∫√(x²+y²)`;
* the L² Cauchy–Schwarz (`integral_cauchy_schwarz_sq`, axiom 5) gives `(∫√(x²+y²))² ≤ 2π·∫(x²+y²)`.
The arithmetic kernel chains these to `4π·A ≤ C²`; transferring across the area/circumference
preservation of the reparametrization gives the result for `γ`. -/
theorem isoperimetric_inequality_regular (γ : RegularClosedCurve)
    (hL : 0 < γ.circumference) :
    4 * π * γ.area ≤ γ.circumference ^ 2 := by
  -- Step 1: constant-speed, zero-mean reparametrization (same circumference and area).
  obtain ⟨ρ, hcirc, harea, hspeed, hzx, hzy⟩ :=
    RegularClosedCurve.exists_nice_reparam_for_regular γ hL
  -- Step 2: the constant speed c = L / (2π).
  set c := γ.circumference / (2 * π) with hc_def
  have hc_pos : 0 < c := div_pos hL (by positivity)
  -- Step 3: the three analytic bounds, on ρ.
  have hWirt : ∫ t in (0 : ℝ)..(2 * π), (ρ.x t ^ 2 + ρ.y t ^ 2) ≤ 2 * π * c ^ 2 :=
    IsoperimetricFourier.wirtinger_sum_bound ρ.x ρ.y ρ.smooth_x ρ.smooth_y
      ρ.periodic_x ρ.periodic_y c hc_pos hspeed hzx hzy
  have hArea2 :
      |∫ t in (0 : ℝ)..(2 * π), (ρ.x t * deriv ρ.y t - ρ.y t * deriv ρ.x t)| ≤
        c * ∫ t in (0 : ℝ)..(2 * π), √(ρ.x t ^ 2 + ρ.y t ^ 2) :=
    IsoperimetricCauchySchwarz.area_cauchy_schwarz_bound_contDiff ρ.x ρ.y c hc_pos.le
      ρ.smooth_x ρ.smooth_y hspeed
  have hCS :
      (∫ t in (0 : ℝ)..(2 * π), √(ρ.x t ^ 2 + ρ.y t ^ 2)) ^ 2 ≤
        2 * π * ∫ t in (0 : ℝ)..(2 * π), (ρ.x t ^ 2 + ρ.y t ^ 2) :=
    IsoperimetricCauchySchwarz.integral_cauchy_schwarz_sq ρ.x ρ.y
      ρ.continuous_x ρ.continuous_y
  -- Step 4: name the two integrals S and Sxy.
  set S := ∫ t in (0 : ℝ)..(2 * π), √(ρ.x t ^ 2 + ρ.y t ^ 2) with hS_def
  set Sxy := ∫ t in (0 : ℝ)..(2 * π), (ρ.x t ^ 2 + ρ.y t ^ 2) with hSxy_def
  -- Step 5: S ≥ 0.
  have hS_nn : 0 ≤ S := by
    rw [hS_def]
    apply intervalIntegral.integral_nonneg (by positivity)
    intro t _
    exact Real.sqrt_nonneg _
  -- Step 6: 2·(ρ.area) = |∫(x·y' − y·x')|, so 2·(ρ.area) ≤ c·S.
  have h2area :
      2 * ρ.area = |∫ t in (0 : ℝ)..(2 * π), (ρ.x t * deriv ρ.y t - ρ.y t * deriv ρ.x t)| := by
    simp only [RegularClosedCurve.area]; ring
  have harea' : 2 * ρ.area ≤ c * S := by rw [h2area]; exact hArea2
  -- Step 7: L = 2πc.
  have hL_eq : γ.circumference = 2 * π * c := by
    rw [hc_def]; field_simp
  -- Step 8: the arithmetic kernel, then transfer across the reparametrization.
  have key : 4 * π * ρ.area ≤ γ.circumference ^ 2 :=
    isoperimetric_arithmetic_kernel ρ.area γ.circumference c S Sxy
      hc_pos hL_eq hS_nn harea' hCS hWirt
  rwa [harea] at key

/-- **Isoperimetric ratio form**: for a regular closed curve with positive area, the
isoperimetric ratio `C² / (4πA)` is at least `1`. -/
theorem isoperimetric_ratio_ge_one (γ : RegularClosedCurve)
    (hL : 0 < γ.circumference) (hA : 0 < γ.area) :
    1 ≤ γ.circumference ^ 2 / (4 * π * γ.area) := by
  have hden : 0 < 4 * π * γ.area := by positivity
  rw [le_div_iff₀ hden, one_mul]
  linarith [isoperimetric_inequality_regular γ hL]

end

end IsoperimetricRegular
