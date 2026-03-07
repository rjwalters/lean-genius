/-
  N-Dimensional Volume from Surface Area Integration
  Open Question: area-of-circle-oq-01-oq-02-oq-01

  Generalizes the 2D result A(r) = ∫₀ʳ C(ρ) dρ to n dimensions:

    V_n(r) = ∫₀ʳ S_n(ρ) dρ

  where S_n(ρ) = n · ω_n · ρ^(n-1) is the (n-1)-sphere surface area
  and ω_n = π^(n/2) / Γ(n/2 + 1) is the unit ball volume.

  The relationship d/dr[V_n(r)] = S_n(r) is the n-dimensional analogue of
  the circumference-area duality C = dA/dr. Integrating recovers V_n(r).

  Proof approach: V_n(r) = ω_n · r^n is a polynomial in r, so differentiation
  gives S_n(r) = n · ω_n · r^(n-1), and FTC Part 2 yields the integral formula.

  Chain: area-of-circle → OQ01 (C = dA/dr) → OQ02 (A = ∫C) → OQ01 (V_n = ∫S_n)

  References:
  - AreaFromCircumferenceIntegral.lean (2D case)
  - AreaOfCircleOQ02.lean (unit ball volume ω_n)
-/

import Mathlib

open Real MeasureTheory

noncomputable section

namespace NDimVolumeIntegral

/- ## Part I: Volume and Surface Area Functions -/

/-- The unit ball volume ω_n = π^(n/2) / Γ(n/2 + 1).
    Redefined here to be self-contained; matches AreaOfCircleOQ02.unitBallVolume. -/
def unitBallVolume (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/-- The n-ball volume function V_n(r) = ω_n · r^n. -/
def nBallVol (n : ℕ) (r : ℝ) : ℝ :=
  unitBallVolume n * r ^ n

/-- The (n-1)-sphere surface area function S_n(r) = n · ω_n · r^(n-1).
    This is the "boundary measure" of the n-ball of radius r.
    For n=2: S₂(r) = 2 · π · r = 2πr (circumference). ✓
    For n=3: S₃(r) = 3 · (4π/3) · r² = 4πr² (sphere surface area). ✓ -/
def nSphereArea (n : ℕ) (r : ℝ) : ℝ :=
  n * unitBallVolume n * r ^ (n - 1)

/- ## Part II: Unit Ball Volume Properties -/

/-- ω_n ≥ 0 for all n. -/
theorem unitBallVolume_nonneg (n : ℕ) : 0 ≤ unitBallVolume n := by
  unfold unitBallVolume
  apply div_nonneg
  · exact rpow_nonneg (le_of_lt pi_pos) _
  · exact le_of_lt (Gamma_pos_of_pos (by positivity))

/-- ω_0 = 1 (a single point). -/
theorem unitBallVolume_zero : unitBallVolume 0 = 1 := by
  unfold unitBallVolume
  simp [Gamma_one]

/-- ω_1 = 2 (the interval [-1,1]). -/
theorem unitBallVolume_one : unitBallVolume 1 = 2 := by
  unfold unitBallVolume
  simp only [Nat.cast_one]
  rw [show (1 : ℝ)/2 + 1 = 3/2 from by ring]
  have h32 : Gamma (3/2 : ℝ) = √π / 2 := by
    have h := Gamma_add_one (show (1/2 : ℝ) ≠ 0 from by norm_num)
    rw [show (1 : ℝ)/2 + 1 = 3/2 from by ring] at h
    rw [h, Gamma_one_half_eq]; ring
  rw [h32, ← Real.sqrt_eq_rpow]
  have h : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp [h.ne']

/-- ω_2 = π (area of the unit disk). -/
theorem unitBallVolume_two : unitBallVolume 2 = π := by
  unfold unitBallVolume
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ)/2 + 1 = 2 from by ring, show (2 : ℝ)/2 = 1 from by ring]
  rw [rpow_one, Gamma_two]
  simp

/-- ω_3 = 4π/3 (volume of the unit 3-ball). -/
theorem unitBallVolume_three : unitBallVolume 3 = 4 * π / 3 := by
  unfold unitBallVolume
  simp only [Nat.cast_ofNat]
  -- Use Gamma recurrence: Γ(5/2) = (3/2)·Γ(3/2) = (3/2)·(√π/2) = 3√π/4
  have h32 : Gamma (3/2 : ℝ) = √π / 2 := by
    have h := Gamma_add_one (show (1/2 : ℝ) ≠ 0 from by norm_num)
    rw [show (1 : ℝ)/2 + 1 = 3/2 from by ring] at h
    rw [h, Gamma_one_half_eq]; ring
  have h52 : Gamma (5/2 : ℝ) = 3 * √π / 4 := by
    have h := Gamma_add_one (show (3/2 : ℝ) ≠ 0 from by norm_num)
    rw [show (3 : ℝ)/2 + 1 = 5/2 from by ring] at h
    rw [h, h32]; ring
  rw [show (3 : ℝ)/2 + 1 = 5/2 from by ring, h52]
  rw [show (3 : ℝ)/2 = (1 : ℝ) + 1/2 from by ring]
  rw [rpow_add pi_pos, rpow_one, ← Real.sqrt_eq_rpow]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp [hpi.ne']
  ring

/- ## Part III: The Derivative Relation d/dr[V_n(r)] = S_n(r) -/

/-- The derivative of r^n is n·r^(n-1) for n ≥ 1.
    This wraps Mathlib's HasDerivAt for natural number powers. -/
theorem hasDerivAt_rpow_nat (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (fun x => x ^ n) (↑n * r ^ (n - 1)) r :=
  hasDerivAt_pow n r

/-- **KEY**: The derivative of V_n(r) = ω_n · r^n is S_n(r) = n · ω_n · r^(n-1).
    This is the n-dimensional generalization of dA/dr = C (= 2πr for n=2). -/
theorem hasDerivAt_nBallVol (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (nBallVol n) (nSphereArea n r) r := by
  unfold nBallVol nSphereArea
  have h := (hasDerivAt_pow n r).const_mul (unitBallVolume n)
  convert h using 1
  ring

/-- The n-ball volume function is continuous. -/
theorem continuous_nBallVol (n : ℕ) : Continuous (nBallVol n) := by
  unfold nBallVol
  exact continuous_const.mul (continuous_pow n)

/-- The n-sphere surface area function is continuous. -/
theorem continuous_nSphereArea (n : ℕ) : Continuous (nSphereArea n) := by
  unfold nSphereArea
  exact continuous_const.mul (continuous_pow (n - 1))

/- ## Part IV: The Integral Formula V_n(r) = ∫₀ʳ S_n(ρ) dρ -/

/-- V_n(0) = 0 for n ≥ 1. -/
theorem nBallVol_zero (n : ℕ) (hn : 1 ≤ n) : nBallVol n 0 = 0 := by
  unfold nBallVol
  simp [zero_pow (by omega : n ≠ 0)]

/-- **MAIN THEOREM**: The n-ball volume equals the integral of surface area.

    V_n(r) = ∫₀ʳ S_n(ρ) dρ

    This is the n-dimensional generalization of A(r) = ∫₀ʳ C(ρ) dρ.

    Proof: By FTC Part 2, since d/dr[V_n(r)] = S_n(r) and S_n is continuous:
      ∫₀ʳ S_n(ρ) dρ = V_n(r) - V_n(0) = V_n(r) - 0 = V_n(r). -/
theorem volume_from_surface_integral (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    ∫ ρ in (0 : ℝ)..r, nSphereArea n ρ = nBallVol n r := by
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) r,
      HasDerivAt (nBallVol n) (nSphereArea n x) x :=
    fun x _ => hasDerivAt_nBallVol n hn x
  have h_int : IntervalIntegrable (nSphereArea n) volume 0 r :=
    (continuous_nSphereArea n).intervalIntegrable 0 r
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int,
      nBallVol_zero n hn, sub_zero]

/-- The derivative of the integral recovers the surface area (FTC Part 1). -/
theorem deriv_volume_integral (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (fun s => ∫ ρ in (0 : ℝ)..s, nSphereArea n ρ)
      (nSphereArea n r) r := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_nSphereArea n).intervalIntegrable 0 r)
    ((continuous_nSphereArea n).stronglyMeasurableAtFilter volume (𝓝 r))
    (continuous_nSphereArea n).continuousAt

/- ## Part V: Special Cases Recover Known Results -/

/-- n=1: V₁(r) = 2r and S₁(r) = 2, so ∫₀ʳ 2 dρ = 2r. -/
theorem volume_from_surface_1d (r : ℝ) :
    ∫ ρ in (0 : ℝ)..r, nSphereArea 1 ρ = nBallVol 1 r :=
  volume_from_surface_integral 1 (le_refl 1) r

/-- n=2: V₂(r) = πr² and S₂(r) = 2πr, so ∫₀ʳ 2πρ dρ = πr².
    This is exactly the classical A(r) = ∫₀ʳ C(ρ) dρ. -/
theorem volume_from_surface_2d (r : ℝ) :
    ∫ ρ in (0 : ℝ)..r, nSphereArea 2 ρ = nBallVol 2 r :=
  volume_from_surface_integral 2 (by norm_num) r

/-- n=3: V₃(r) = (4π/3)r³ and S₃(r) = 4πr², so ∫₀ʳ 4πρ² dρ = (4π/3)r³.
    This is the familiar 3D formula for sphere volume from surface area. -/
theorem volume_from_surface_3d (r : ℝ) :
    ∫ ρ in (0 : ℝ)..r, nSphereArea 3 ρ = nBallVol 3 r :=
  volume_from_surface_integral 3 (by norm_num) r

/-- The 2D surface area function S₂(r) = 2πr matches the circumference. -/
theorem nSphereArea_two (r : ℝ) : nSphereArea 2 r = 2 * unitBallVolume 2 * r := by
  unfold nSphereArea
  simp

/-- The 2D volume function V₂(r) = πr² matches the circle area. -/
theorem nBallVol_two (r : ℝ) : nBallVol 2 r = unitBallVolume 2 * r ^ 2 := rfl

/-- With ω₂ = π: S₂(r) = 2πr. -/
theorem nSphereArea_two_explicit (r : ℝ) : nSphereArea 2 r = 2 * π * r := by
  rw [nSphereArea_two, unitBallVolume_two]

/-- With ω₂ = π: V₂(r) = πr². -/
theorem nBallVol_two_explicit (r : ℝ) : nBallVol 2 r = π * r ^ 2 := by
  rw [nBallVol_two, unitBallVolume_two]

/-- The 3D surface area S₃(r) = 4πr² (sphere surface area formula). -/
theorem nSphereArea_three_explicit (r : ℝ) : nSphereArea 3 r = 4 * π * r ^ 2 := by
  unfold nSphereArea
  rw [unitBallVolume_three]
  push_cast; ring

/-- The 3D volume V₃(r) = (4π/3)r³ (sphere volume formula). -/
theorem nBallVol_three_explicit (r : ℝ) : nBallVol 3 r = 4 * π / 3 * r ^ 3 := by
  unfold nBallVol
  rw [unitBallVolume_three]

/- ## Part VI: Annulus / Shell Generalization -/

/-- The volume of an n-dimensional shell (annulus) between radii r₁ and r₂:
    ∫_{r₁}^{r₂} S_n(ρ) dρ = V_n(r₂) - V_n(r₁). -/
theorem shell_volume (n : ℕ) (hn : 1 ≤ n) (r₁ r₂ : ℝ) :
    ∫ ρ in r₁..r₂, nSphereArea n ρ = nBallVol n r₂ - nBallVol n r₁ := by
  have h_deriv : ∀ x ∈ Set.uIcc r₁ r₂,
      HasDerivAt (nBallVol n) (nSphereArea n x) x :=
    fun x _ => hasDerivAt_nBallVol n hn x
  have h_int : IntervalIntegrable (nSphereArea n) volume r₁ r₂ :=
    (continuous_nSphereArea n).intervalIntegrable r₁ r₂
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int

/-- The 3D spherical shell between r₁ and r₂:
    ∫_{r₁}^{r₂} 4πρ² dρ = (4π/3)(r₂³ - r₁³). -/
theorem shell_volume_3d (r₁ r₂ : ℝ) :
    ∫ ρ in r₁..r₂, nSphereArea 3 ρ = nBallVol 3 r₂ - nBallVol 3 r₁ :=
  shell_volume 3 (by norm_num) r₁ r₂

/- ## Part VII: Scaling Properties -/

/-- V_n(cr) = c^n · V_n(r): the n-ball volume scales as the n-th power of radius. -/
theorem nBallVol_scaling (n : ℕ) (c r : ℝ) :
    nBallVol n (c * r) = c ^ n * nBallVol n r := by
  unfold nBallVol
  rw [mul_pow, mul_comm (c ^ n), mul_assoc]

/-- S_n(cr) = c^(n-1) · S_n(r): the surface area scales as the (n-1)-th power. -/
theorem nSphereArea_scaling (n : ℕ) (c r : ℝ) :
    nSphereArea n (c * r) = c ^ (n - 1) * nSphereArea n r := by
  unfold nSphereArea
  rw [mul_pow, mul_comm (c ^ (n-1)), ← mul_assoc, ← mul_assoc]

/-- The ratio S_n(r) / V_n(r) = n/r for r ≠ 0 and n ≥ 1.
    This is the n-dimensional generalization of C/A = 2/r. -/
theorem surface_to_volume_ratio (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : r ≠ 0) :
    nSphereArea n r / nBallVol n r = n / r := by
  unfold nSphereArea nBallVol
  have hω : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    apply div_ne_zero
    · exact (rpow_pos_of_pos pi_pos _).ne'
    · exact (Gamma_pos_of_pos (by positivity)).ne'
  have hrn : r ^ n ≠ 0 := pow_ne_zero n hr
  field_simp [hω, hrn, hr]
  rw [show r ^ (n - 1) * (unitBallVolume n * r ^ n)⁻¹ =
    (unitBallVolume n)⁻¹ * (r ^ (n - 1) * (r ^ n)⁻¹) from by ring]
  rw [← pow_sub₀ hr (by omega : n - 1 ≤ n)]
  simp [show n - (n - 1) = 1 from by omega]
  ring

/- ## Part VIII: Summary

### Proved (0 sorries, 0 axioms):
1. `hasDerivAt_nBallVol` — d/dr[V_n(r)] = S_n(r)  (power rule)
2. `volume_from_surface_integral` — V_n(r) = ∫₀ʳ S_n(ρ) dρ  (**MAIN THEOREM**, FTC)
3. `deriv_volume_integral` — d/dr[∫₀ʳ S_n] = S_n(r)  (FTC Part 1)
4. `shell_volume` — ∫_{r₁}^{r₂} S_n(ρ) dρ = V_n(r₂) - V_n(r₁)  (shell/annulus)
5. Special cases: n=1 (2r), n=2 (πr²), n=3 ((4π/3)r³)
6. Explicit formulas: S₂ = 2πr, S₃ = 4πr², V₃ = (4π/3)r³
7. Scaling: V_n(cr) = c^n V_n(r), S_n(cr) = c^(n-1) S_n(r)
8. Surface-to-volume ratio: S_n/V_n = n/r

### Key Insight:
The n-dimensional volume-surface duality V_n' = S_n is a direct generalization
of the 2D circumference-area duality A' = C. Both follow from the polynomial
structure V_n(r) = ω_n · r^n, making the FTC proof completely routine.

### Dimensions of the OQ Chain:
- AreaOfCircle (Wiedijk #9): A = πr² proved via integral
- OQ01 (CircumferenceFromArea): C = dA/dr = 2πr
- OQ02 (AreaFromCircumferenceIntegral): A = ∫₀ʳ C(ρ) dρ
- **OQ01 of OQ02 (THIS FILE)**: V_n = ∫₀ʳ S_n(ρ) dρ (n-dimensional generalization)
-/

end NDimVolumeIntegral

end
