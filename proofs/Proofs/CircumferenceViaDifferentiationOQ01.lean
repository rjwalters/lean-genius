/-
  OQ-01: n-Dimensional Surface Area via Differentiation of Volume
  (circumference-via-differentiation-oq-01)

  For the n-ball with volume V_n(r) = ω_n · rⁿ (where ω_n = π^(n/2)/Γ(n/2+1)
  is the unit ball volume), the derivative with respect to r equals the
  (n-1)-sphere surface area:

    dV_n/dr = n · ω_n · r^(n-1) = S_{n-1}(r)

  Special cases:
    n=2: d(πr²)/dr = 2πr  (circumference of circle — parent theorem)
    n=3: d(4πr³/3)/dr = 4πr²  (surface area of sphere)

  The surface area constant n·ω_n equals 2π^(n/2)/Γ(n/2) via the Gamma
  recursion Γ(n/2+1) = (n/2)·Γ(n/2).

  This file is self-contained: no dependency on AreaOfCircleOQ02.
  Status: 0 sorries, 0 axioms.
-/

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic
import Proofs.CircumferenceViaDifferentiation

open Real MeasureTheory

noncomputable section

namespace CircumferenceViaDifferentiationOQ01

-- ============================================================
-- Local Definition of Unit n-Ball Volume
-- ============================================================

/-- The volume of the unit n-ball: ω_n = π^(n/2) / Γ(n/2+1).
    Special values: ω_0 = 1, ω_1 = 2, ω_2 = π, ω_3 = 4π/3. -/
def unitBallVolume (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/-- The unit ball volume is non-negative. -/
theorem unitBallVolume_nonneg (n : ℕ) : 0 ≤ unitBallVolume n :=
  div_nonneg (rpow_nonneg pi_nonneg _) (le_of_lt (Gamma_pos_of_pos (by positivity)))

/-- ω_2 = π (the area of the unit disk). -/
theorem unitBallVolume_two : unitBallVolume 2 = π := by
  unfold unitBallVolume
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ) / 2 + 1 = 2 from by norm_num, show (2 : ℝ) / 2 = 1 from by norm_num]
  rw [rpow_one, Gamma_two]
  simp

/-- Helper: Γ(3/2) = √π/2. -/
private lemma gamma_three_halves : Gamma (3 / 2 : ℝ) = √π / 2 := by
  have h := Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 from by norm_num)
  rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by norm_num] at h
  rw [h, Gamma_one_half_eq]; ring

/-- Helper: Γ(5/2) = 3√π/4. -/
private lemma gamma_five_halves : Gamma (5 / 2 : ℝ) = 3 * √π / 4 := by
  have h := Gamma_add_one (show (3 / 2 : ℝ) ≠ 0 from by norm_num)
  rw [show (3 : ℝ) / 2 + 1 = 5 / 2 from by norm_num] at h
  rw [h, gamma_three_halves]; ring

/-- ω_3 = 4π/3 (the volume of the unit 3-ball). -/
theorem unitBallVolume_three : unitBallVolume 3 = 4 * π / 3 := by
  unfold unitBallVolume
  simp only [Nat.cast_ofNat]
  rw [show (3 : ℝ) / 2 + 1 = 5 / 2 from by norm_num, gamma_five_halves]
  -- Goal: π ^ (3/2) / (3 * √π / 4) = 4 * π / 3
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 from by norm_num]
  rw [rpow_add pi_pos, rpow_one, ← Real.sqrt_eq_rpow]
  have hsqrt : √π ≠ 0 := Real.sqrt_ne_zero'.mpr pi_pos
  field_simp [hsqrt]; ring

-- ============================================================
-- Main Definitions
-- ============================================================

/-- The n-ball volume as a function of radius r.
    V_n(r) = ω_n · rⁿ where ω_n = π^(n/2)/Γ(n/2+1). -/
def nBallVolumeFn (n : ℕ) (r : ℝ) : ℝ := unitBallVolume n * r ^ n

/-- The surface area constant: n times the unit n-ball volume.
    C_n = n · ω_n = 2π^(n/2)/Γ(n/2). -/
def nSphereSurfaceConst (n : ℕ) : ℝ := n * unitBallVolume n

/-- The (n-1)-sphere surface area as a function of radius. -/
def nSphereSurfaceFn (n : ℕ) (r : ℝ) : ℝ := nSphereSurfaceConst n * r ^ (n - 1)

-- ============================================================
-- Part 1: The Main Derivative Theorem
-- ============================================================

/-- **Main theorem**: The n-ball volume function has derivative equal to the
    surface area at every r.

    dV_n/dr(r) = n · ω_n · r^(n-1) = S_{n-1}(r)

    Proof: Power rule d/dr(rⁿ) = n·rⁿ⁻¹, scaled by ω_n. -/
theorem nBallVolumeFn_hasDerivAt (n : ℕ) (r : ℝ) :
    HasDerivAt (nBallVolumeFn n) (nSphereSurfaceFn n r) r := by
  unfold nBallVolumeFn nSphereSurfaceFn nSphereSurfaceConst
  have h := (hasDerivAt_pow n r).const_mul (unitBallVolume n)
  have heq : unitBallVolume n * (↑n * r ^ (n - 1)) =
             ↑n * unitBallVolume n * r ^ (n - 1) := by ring
  rwa [heq] at h

/-- The volume function is differentiable everywhere. -/
theorem nBallVolumeFn_differentiable (n : ℕ) : Differentiable ℝ (nBallVolumeFn n) :=
  fun r => (nBallVolumeFn_hasDerivAt n r).differentiableAt

/-- The `deriv` of the volume function equals the surface area function pointwise. -/
theorem deriv_nBallVolume (n : ℕ) (r : ℝ) :
    deriv (nBallVolumeFn n) r = nSphereSurfaceFn n r :=
  (nBallVolumeFn_hasDerivAt n r).deriv

-- ============================================================
-- Part 2: Gamma Recursion Gives the Surface Area Formula
-- ============================================================

/-- For n ≥ 1, the surface constant equals 2π^(n/2) / Γ(n/2).

    n · ω_n = n · π^(n/2)/Γ(n/2+1) = n · π^(n/2)/((n/2)·Γ(n/2)) = 2π^(n/2)/Γ(n/2). -/
theorem nSphereSurfaceConst_eq_gamma (n : ℕ) (hn : 0 < n) :
    nSphereSurfaceConst n = 2 * π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2) := by
  unfold nSphereSurfaceConst unitBallVolume
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn2ne : (n : ℝ) / 2 ≠ 0 := div_ne_zero hn_pos.ne' two_ne_zero
  have hGne : Gamma ((n : ℝ) / 2) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  rw [Gamma_add_one hn2ne]
  field_simp [hGne, hn_pos.ne', hn2ne]
  ring

-- ============================================================
-- Part 3: Special Values of the Surface Area Constant
-- ============================================================

/-- n=2: Surface constant = 2π (circumference of the unit circle). -/
theorem nSphereSurfaceConst_two : nSphereSurfaceConst 2 = 2 * π := by
  unfold nSphereSurfaceConst
  rw [unitBallVolume_two]
  norm_num

/-- n=3: Surface constant = 4π (surface area of the unit 2-sphere). -/
theorem nSphereSurfaceConst_three : nSphereSurfaceConst 3 = 4 * π := by
  unfold nSphereSurfaceConst
  rw [unitBallVolume_three]
  norm_num

-- ============================================================
-- Part 4: Concrete Derivative Theorems for n=2 and n=3
-- ============================================================

/-- **n=2**: Derivative of disk area πr² = circumference 2πr. -/
theorem disk_area_deriv_eq_circumference (r : ℝ) :
    HasDerivAt (nBallVolumeFn 2) (2 * π * r) r := by
  have h := nBallVolumeFn_hasDerivAt 2 r
  convert h using 1
  unfold nSphereSurfaceFn; rw [nSphereSurfaceConst_two]; norm_num

/-- **n=3**: Derivative of ball volume (4π/3)r³ = sphere surface 4πr². -/
theorem ball_volume_deriv_eq_sphere_surface (r : ℝ) :
    HasDerivAt (nBallVolumeFn 3) (4 * π * r ^ 2) r := by
  have h := nBallVolumeFn_hasDerivAt 3 r
  convert h using 1
  unfold nSphereSurfaceFn; rw [nSphereSurfaceConst_three]; norm_num

-- ============================================================
-- Part 5: Connection to Parent (CircumferenceViaDifferentiation)
-- ============================================================

/-- The n=2 volume function matches the parent's area function. -/
theorem nBallVolumeFn_two_eq_areaFn (r : ℝ) :
    nBallVolumeFn 2 r = CircumferenceViaDifferentiation.areaFn r := by
  unfold nBallVolumeFn CircumferenceViaDifferentiation.areaFn
  rw [unitBallVolume_two]

/-- The parent's circumference theorem is the n=2 special case. -/
theorem disk_area_matches_parent (r : ℝ) :
    HasDerivAt CircumferenceViaDifferentiation.areaFn
               (CircumferenceViaDifferentiation.circumferenceFn r) r := by
  have h := disk_area_deriv_eq_circumference r
  rw [← nBallVolumeFn_two_eq_areaFn] at h
  convert h using 1
  unfold CircumferenceViaDifferentiation.circumferenceFn; ring

-- ============================================================
-- Part 6: Volume and Surface Properties
-- ============================================================

/-- Surface area of the unit (n-1)-sphere = the surface area constant. -/
theorem nSphereSurface_unit (n : ℕ) : nSphereSurfaceFn n 1 = nSphereSurfaceConst n := by
  unfold nSphereSurfaceFn; simp

/-- Unit ball volume in terms of surface constant (for n ≥ 1). -/
theorem unitBallVolume_from_surface (n : ℕ) (hn : 0 < n) :
    unitBallVolume n = nSphereSurfaceConst n / n := by
  unfold nSphereSurfaceConst
  field_simp [(Nat.cast_pos.mpr hn).ne']

/-- The n-ball volume function is nonneg for nonneg radius. -/
theorem nBallVolumeFn_nonneg (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ nBallVolumeFn n r :=
  mul_nonneg (unitBallVolume_nonneg n) (pow_nonneg hr n)

end CircumferenceViaDifferentiationOQ01

end -- section

-- ============================================================
-- Examples
-- ============================================================

open CircumferenceViaDifferentiationOQ01

-- n=2: volume function is πr²
example (r : ℝ) : nBallVolumeFn 2 r = Real.pi * r ^ 2 := by
  unfold nBallVolumeFn; rw [unitBallVolume_two]

-- n=3: volume function is (4π/3)r³
example (r : ℝ) : nBallVolumeFn 3 r = (4 * Real.pi / 3) * r ^ 3 := by
  unfold nBallVolumeFn; rw [unitBallVolume_three]; ring

-- Derivative at r=1 for n=2 is 2π
example : deriv (nBallVolumeFn 2) 1 = 2 * Real.pi := by
  rw [deriv_nBallVolume, nSphereSurfaceConst_two]
  unfold nSphereSurfaceFn; norm_num

-- Surface area constants
example : nSphereSurfaceConst 2 = 2 * Real.pi := nSphereSurfaceConst_two
example : nSphereSurfaceConst 3 = 4 * Real.pi := nSphereSurfaceConst_three

#check @CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt
