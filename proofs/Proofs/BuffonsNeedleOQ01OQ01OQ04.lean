/-
  Higher-Dimensional Cauchy–Crofton Formula
  Open Question: buffons-needle-oq-01-oq-01-oq-04

  Generalizes the 2D Buffon–Barbier formula E[crossings] = 2L/(πd) to curves
  in ℝⁿ intersecting random hyperplane grids. The n-dimensional formula is:

      E[crossings] = c_n · L(γ) / d

  where c_n = 2σ_{n-2} / ((n-1) · σ_{n-1}) and σ_k is the surface area of S^k.

  Main results:
  1. Sphere surface area σ_n = 2π^{(n+1)/2} / Γ((n+1)/2)
  2. Cauchy–Crofton constant c_n and its special values
  3. Angular averaging on RP^{n-1} (axiomatized, needs sphere measure)
  4. n-dimensional Cauchy–Crofton formula from angular averaging
  5. Recovery of the 2D Buffon–Barbier formula as the n=2 case
  6. Explicit constants: c_2 = 2/π, c_3 = 1/2, c_4 = 4/(3π)

  References:
  - Cauchy, A. "Mémoire sur la rectification des courbes" (1832, 1841)
  - Crofton, M.W. "On the theory of local probability" (1868)
  - Santaló, L.A. "Integral Geometry and Geometric Probability" (1976), Ch. 14
  - Parent: BuffonsNeedleOQ01OQ01.lean (2D angular average)
-/

import Mathlib

open Real MeasureTheory

namespace CauchyCrofton

/-
## Part I: Sphere Surface Area

The surface area of S^n (the n-sphere in ℝ^{n+1}) is:
  σ_n = 2π^{(n+1)/2} / Γ((n+1)/2)
-/

/-- Surface area of the unit n-sphere S^n ⊂ ℝ^{n+1}.
    σ_n = 2π^{(n+1)/2} / Γ((n+1)/2).
    Convention: σ_{-1} is not defined; σ_0 = 2 (two endpoints of S^0). -/
noncomputable def sphereArea (n : ℕ) : ℝ :=
  2 * π ^ (((n : ℝ) + 1) / 2) / Gamma (((n : ℝ) + 1) / 2)

/-- σ_n is positive for all n. -/
theorem sphereArea_pos (n : ℕ) : 0 < sphereArea n := by
  unfold sphereArea
  apply div_pos
  · apply mul_pos two_pos
    exact rpow_pos_of_pos pi_pos _
  · exact Gamma_pos_of_pos (by positivity)

/-- σ_0 = 2 (two points of S^0 = {-1, 1}).
    Proof: 2π^{1/2}/Γ(1/2) = 2√π/√π = 2. -/
theorem sphereArea_zero : sphereArea 0 = 2 := by
  unfold sphereArea
  simp only [Nat.cast_zero, zero_add]
  rw [show (1 : ℝ) / 2 = 1 / 2 from rfl]
  rw [Gamma_one_half_eq, ← Real.sqrt_eq_rpow]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr pi_pos
  field_simp [hpi.ne']

/-- σ_1 = 2π (circumference of S^1).
    Proof: 2π^1/Γ(1) = 2π/1 = 2π. -/
theorem sphereArea_one : sphereArea 1 = 2 * π := by
  unfold sphereArea
  simp only [Nat.cast_one]
  rw [show (1 + 1 : ℝ) / 2 = 1 from by ring]
  rw [rpow_one, Gamma_one]
  ring

/-- σ_2 = 4π (surface area of S^2).
    Proof: 2π^{3/2}/Γ(3/2) = 2π^{3/2}/(√π/2) = 4π. -/
theorem sphereArea_two : sphereArea 2 = 4 * π := by
  unfold sphereArea
  simp only [Nat.cast_ofNat]
  rw [show (2 + 1 : ℝ) / 2 = 3 / 2 from by ring]
  have h32 : Gamma (3 / 2 : ℝ) = √π / 2 := by
    have h := Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 from by norm_num)
    rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring] at h
    rw [h, Gamma_one_half_eq]; ring
  rw [h32]
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 from by ring, rpow_add pi_pos, rpow_one]
  rw [show (1 : ℝ) / 2 = 1 / 2 from rfl, ← Real.sqrt_eq_rpow]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr pi_pos
  field_simp [hpi.ne']
  ring

/-- σ_3 = 2π² (surface area of S^3 ⊂ ℝ⁴).
    Proof: 2π^{4/2}/Γ(4/2) = 2π²/Γ(2) = 2π²/1 = 2π². -/
theorem sphereArea_three : sphereArea 3 = 2 * π ^ 2 := by
  unfold sphereArea
  simp only [Nat.cast_ofNat]
  rw [show (3 + 1 : ℝ) / 2 = 2 from by norm_num]
  rw [show Gamma (2 : ℝ) = 1 from by
    rw [show (2 : ℝ) = 1 + 1 from by norm_num, Gamma_add_one one_ne_zero, Gamma_one, mul_one]]
  rw [rpow_natCast]
  ring

/-- σ_4 = 8π²/3 (surface area of S^4 ⊂ ℝ^5).
    Proof: 2π^{5/2}/Γ(5/2) = 2π^{5/2}/((3/4)√π) = 8π²/3. -/
theorem sphereArea_four : sphereArea 4 = 8 * π ^ 2 / 3 := by
  unfold sphereArea
  simp only [Nat.cast_ofNat]
  rw [show (4 + 1 : ℝ) / 2 = 5 / 2 from by ring]
  have h52 : Gamma (5 / 2 : ℝ) = 3 / 4 * √π := by
    have h32 := Gamma_add_one (show (3 / 2 : ℝ) ≠ 0 from by norm_num)
    rw [show (3 : ℝ) / 2 + 1 = 5 / 2 from by ring] at h32
    rw [h32]
    have h12 := Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 from by norm_num)
    rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring] at h12
    rw [h12, Gamma_one_half_eq]; ring
  rw [h52, show (5 : ℝ) / 2 = 2 + 1 / 2 from by ring, rpow_add pi_pos, rpow_natCast,
      ← Real.sqrt_eq_rpow]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr pi_pos
  field_simp [hpi.ne']
  ring

/-- σ_5 = π³ (surface area of S^5 ⊂ ℝ^6).
    Proof: 2π^3/Γ(3) = 2π^3/2 = π^3. -/
theorem sphereArea_five : sphereArea 5 = π ^ 3 := by
  unfold sphereArea
  simp only [Nat.cast_ofNat]
  rw [show (5 + 1 : ℝ) / 2 = 3 from by ring]
  rw [show Gamma (3 : ℝ) = 2 from by
    rw [show (3 : ℝ) = 2 + 1 from by norm_num,
        Gamma_add_one (show (2 : ℝ) ≠ 0 from by norm_num),
        show (2 : ℝ) = 1 + 1 from by norm_num, Gamma_add_one one_ne_zero, Gamma_one]; ring]
  rw [rpow_natCast]; ring

/-- The n-sphere/n-ball relationship: σ_{n-1} = n · ω_n where
    ω_n = π^{n/2}/Γ(n/2+1) is the unit n-ball volume.
    This is because differentiating Vol(B^n(r)) = ω_n r^n gives
    σ_{n-1} · r^{n-1} = n · ω_n · r^{n-1}. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

theorem unitBallVolume_pos (n : ℕ) : 0 < unitBallVolume n := by
  unfold unitBallVolume
  apply div_pos
  · exact rpow_pos_of_pos pi_pos _
  · exact Gamma_pos_of_pos (by positivity)

/-
## Part II: The Cauchy–Crofton Constant

The n-dimensional constant relating expected crossings to arc length:
  c_n = 2σ_{n-2} / ((n-1) · σ_{n-1})

This arises from the angular averaging integral:
  ∫_{RP^{n-1}} |⟨v, ω⟩| dω = (σ_{n-2}/(n-1)) · ‖v‖

where the integration is over the projective sphere (unoriented hyperplane normals).
-/

/-- The Cauchy–Crofton constant: c_n = 2σ_{n-2} / ((n-1) · σ_{n-1}), for n ≥ 2.
    This gives the expected number of crossings per unit length per unit spacing. -/
noncomputable def cauchyCroftonConst (n : ℕ) : ℝ :=
  2 * sphereArea (n - 2) / ((n - 1 : ℝ) * sphereArea (n - 1))

/-- c_2 = 2/π: the 2D Buffon–Barbier constant.
    Proof: c_2 = 2σ_0 / (1 · σ_1) = 2·2/(1·2π) = 4/(2π) = 2/π. -/
theorem cauchyCrofton_two : cauchyCroftonConst 2 = 2 / π := by
  unfold cauchyCroftonConst
  simp only [show (2 : ℕ) - 2 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl]
  rw [sphereArea_zero, sphereArea_one]
  push_cast
  have hpi : (0 : ℝ) < π := pi_pos
  field_simp [hpi.ne']
  ring

/-- c_3 = 1/2: the 3D crossing constant.
    Proof: c_3 = 2σ_1 / (2 · σ_2) = 2·2π/(2·4π) = 4π/(8π) = 1/2. -/
theorem cauchyCrofton_three : cauchyCroftonConst 3 = 1 / 2 := by
  unfold cauchyCroftonConst
  simp only [show (3 : ℕ) - 2 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl]
  rw [sphereArea_one, sphereArea_two]
  push_cast
  have hpi : (0 : ℝ) < π := pi_pos
  field_simp [hpi.ne']
  ring

/-- c_4 = 4/(3π): the 4D crossing constant.
    Proof: c_4 = 2σ_2 / (3 · σ_3) = 2·4π / (3·2π²) = 8π/(6π²) = 4/(3π). -/
theorem cauchyCrofton_four : cauchyCroftonConst 4 = 4 / (3 * π) := by
  unfold cauchyCroftonConst
  simp only [show (4 : ℕ) - 2 = 2 from rfl, show (4 : ℕ) - 1 = 3 from rfl]
  rw [sphereArea_two, sphereArea_three]
  push_cast
  have hpi : (0 : ℝ) < π := pi_pos
  field_simp [hpi.ne']
  ring

/-- c_5 = 3/8: the 5D crossing constant.
    Proof: c_5 = 2σ_3/(4·σ_4) = 2·2π²/(4·8π²/3) = 3/8. -/
theorem cauchyCrofton_five : cauchyCroftonConst 5 = 3 / 8 := by
  unfold cauchyCroftonConst
  simp only [show (5 : ℕ) - 2 = 3 from rfl, show (5 : ℕ) - 1 = 4 from rfl]
  rw [sphereArea_three, sphereArea_four]
  push_cast
  have hpi2 : (π : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp [hpi2]
  ring

/-- c_6 = 16/(15π): the 6D crossing constant.
    Proof: c_6 = 2σ_4/(5·σ_5) = 2·8π²/3/(5·π³) = 16/(15π). -/
theorem cauchyCrofton_six : cauchyCroftonConst 6 = 16 / (15 * π) := by
  unfold cauchyCroftonConst
  simp only [show (6 : ℕ) - 2 = 4 from rfl, show (6 : ℕ) - 1 = 5 from rfl]
  rw [sphereArea_four, sphereArea_five]
  push_cast
  have hpi : (0 : ℝ) < π := pi_pos
  have hpi3 : (π : ℝ) ^ 3 ≠ 0 := by positivity
  field_simp [hpi.ne', hpi3]
  ring

/-- c_n is positive for n ≥ 2. -/
theorem cauchyCroftonConst_pos (n : ℕ) (hn : 2 ≤ n) : 0 < cauchyCroftonConst n := by
  unfold cauchyCroftonConst
  apply div_pos
  · exact mul_pos two_pos (sphereArea_pos _)
  · apply mul_pos
    · exact Nat.cast_pos.mpr (by omega)
    · exact sphereArea_pos _

/-
## Part III: Angular Averaging on the Projective Sphere (Axiomatized)

The key analytic identity: for v ∈ ℝⁿ,
  ∫_{RP^{n-1}} |⟨v, ω⟩| dω = (σ_{n-2}/(n-1)) · ‖v‖

This requires integration on the unit sphere with respect to the
surface measure, which is not available in Mathlib. We axiomatize
it via a structure that captures the essential properties.
-/

/-- Data packaging the angular average identity on the projective sphere RP^{n-1}.
    This axiomatizes the sphere integral that Mathlib currently lacks. -/
structure AngularAverageData (n : ℕ) where
  /-- The angular average of |⟨v, ω⟩| over RP^{n-1} for a vector v.
      This is ∫_{RP^{n-1}} |⟨v, ω⟩| dω, normalized by the measure of RP^{n-1}. -/
  angularAvg : ℝ → ℝ  -- maps ‖v‖ to the angular average
  /-- The angular average is proportional to ‖v‖. -/
  angularAvg_eq : ∀ r : ℝ, 0 ≤ r → angularAvg r = sphereArea (n - 2) / (n - 1 : ℝ) * r
  /-- The angular average is non-negative. -/
  angularAvg_nonneg : ∀ r : ℝ, 0 ≤ r → 0 ≤ angularAvg r

/-
## Part IV: The n-Dimensional Cauchy–Crofton Formula
-/

variable {n : ℕ} (A : AngularAverageData n) (hn : 2 ≤ n)

/-- **n-Dimensional expected crossings**: For a curve in ℝⁿ with arc length L
    and a random hyperplane grid with spacing d, the expected number of
    crossings is c_n · L / d.

    This formulation takes L (arc length) and d (grid spacing) as parameters,
    abstracting over the specific curve parametrization. -/
noncomputable def expectedCrossings (L d : ℝ) : ℝ :=
  cauchyCroftonConst n * L / d

/-- The expected crossings formula factors through the angular average.
    E[crossings] = (2 / (σ_{n-1} · d)) · ∫_curve angularAvg(‖γ'(t)‖) dt
                 = (2 / (σ_{n-1} · d)) · (σ_{n-2}/(n-1)) · L
                 = c_n · L / d -/
theorem expectedCrossings_eq_angularAvg (L d : ℝ) (hd : 0 < d) (hL : 0 ≤ L) :
    expectedCrossings (n := n) L d =
    2 / (sphereArea (n - 1) * d) * (A.angularAvg L) := by
  unfold expectedCrossings cauchyCroftonConst
  rw [A.angularAvg_eq L hL]
  have hσ : 0 < sphereArea (n - 1) := sphereArea_pos _
  field_simp [hσ.ne', hd.ne']
  ring

/-- For n=2: the expected crossings formula gives 2L/(πd),
    recovering the 2D Buffon–Barbier result. -/
theorem expectedCrossings_dim2 (L d : ℝ) (hd : 0 < d) :
    expectedCrossings (n := 2) L d = 2 * L / (π * d) := by
  unfold expectedCrossings
  rw [cauchyCrofton_two]
  have hpi : (0 : ℝ) < π := pi_pos
  field_simp [hpi.ne', hd.ne']
  ring

/-- For n=3: expected crossings is L/(2d).
    A curve in 3D crossing random planes. -/
theorem expectedCrossings_dim3 (L d : ℝ) (hd : 0 < d) :
    expectedCrossings (n := 3) L d = L / (2 * d) := by
  unfold expectedCrossings
  rw [cauchyCrofton_three]
  field_simp [hd.ne']
  ring

/-- For n=4: expected crossings is 4L/(3πd).
    A curve in 4D crossing random hyperplanes. -/
theorem expectedCrossings_dim4 (L d : ℝ) (hd : 0 < d) :
    expectedCrossings (n := 4) L d = 4 * L / (3 * π * d) := by
  unfold expectedCrossings
  rw [cauchyCrofton_four]
  have hpi : (0 : ℝ) < π := pi_pos
  field_simp [hpi.ne', hd.ne']
  ring

/-- The expected crossings scale linearly with arc length. -/
theorem expectedCrossings_linear (L₁ L₂ d : ℝ) (hd : 0 < d) :
    expectedCrossings (n := n) (L₁ + L₂) d =
    expectedCrossings (n := n) L₁ d + expectedCrossings (n := n) L₂ d := by
  unfold expectedCrossings
  ring

/-- The expected crossings scale inversely with grid spacing. -/
theorem expectedCrossings_scaling (L d λ : ℝ) (hd : 0 < d) (hλ : 0 < λ) :
    expectedCrossings (n := n) L (λ * d) =
    expectedCrossings (n := n) L d / λ := by
  unfold expectedCrossings
  field_simp [hd.ne', hλ.ne', (mul_pos hλ hd).ne']
  ring

/-
## Part V: The Dimension Ladder

The constants c_n satisfy a recurrence related to the sphere area recurrence.
The ratio σ_n/σ_{n-1} controls the geometry.
-/

/-- The sphere area recurrence: σ_n = 2π/(n-1) · σ_{n-2} for n ≥ 2.
    This follows from Γ((n+1)/2) = ((n-1)/2) · Γ((n-1)/2). -/
theorem sphereArea_recurrence (n : ℕ) (hn : 2 ≤ n) :
    sphereArea n = 2 * π / ((n : ℝ) - 1) * sphereArea (n - 2) := by
  unfold sphereArea
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn1_ne : (n : ℝ) - 1 ≠ 0 := hn1_pos.ne'
  have h_cast : ((n : ℕ) : ℝ) + 1 = ((n - 2 : ℕ) : ℝ) + 3 := by push_cast; omega
  rw [show ((n : ℝ) + 1) / 2 = (((n - 2 : ℕ) : ℝ) + 1) / 2 + 1 from by rw [h_cast]; ring]
  rw [show (((n - 2 : ℕ) : ℝ) + 1) / 2 = ((n : ℝ) - 1) / 2 from by push_cast; omega]
  rw [Gamma_add_one (show ((n : ℝ) - 1) / 2 ≠ 0 from by positivity)]
  rw [rpow_add pi_pos, rpow_one]
  have hG : Gamma (((n : ℝ) - 1) / 2) ≠ 0 := (Gamma_pos_of_pos (by positivity)).ne'
  field_simp [hn1_ne, hG]
  ring

/-
## Part VI: Consistency Check — Recovering 2D from General Formula

When n = 2, the formula should match BuffonsNeedleOQ01OQ01:
  E[crossings] = (1/(πd)) · ∫_a^b ∫_0^π |⟨γ'(t), e_θ⟩| dθ dt = 2L/(πd)

The inner integral ∫_0^π |a sin θ + b cos θ| dθ = 2√(a²+b²)
is exactly the 2D angular average: σ_0/1 · ‖v‖ = 2‖v‖.

So the general formula specializes correctly:
  c_2 · L / d = (2/π) · L / d = 2L/(πd) ✓
-/

/-- The angular averaging constant in 2D matches the explicit integral.
    σ_0 / (2-1) = 2/1 = 2, which is the factor in ∫_0^π |sin(θ+c)| dθ = 2. -/
theorem angular_constant_dim2 :
    sphereArea (2 - 2) / ((2 : ℝ) - 1) = 2 := by
  simp [sphereArea_zero]

/-- Expected crossings at unit distance: c_n · L gives crossings per unit
    grid spacing. For n=2 and a unit circle (L = 2π):
    c_2 · 2π = (2/π) · 2π = 4. A unit circle crosses a line grid with
    spacing 1 on average 4 times (2 entry + 2 exit). -/
theorem unit_circle_crossings :
    expectedCrossings (n := 2) (2 * π) 1 = 4 := by
  unfold expectedCrossings
  rw [cauchyCrofton_two]
  have hpi : (0 : ℝ) < π := pi_pos
  field_simp [hpi.ne']
  ring

/-- A line segment of length L in any dimension crosses a hyperplane grid
    with spacing d at most L/d + 1 times. For our formula:
    c_n · L / d ≤ L / d (since c_n ≤ 1 for n ≥ 2). -/
theorem cauchyCrofton_le_one_dim2 : cauchyCroftonConst 2 ≤ 1 := by
  rw [cauchyCrofton_two]
  rw [div_le_one pi_pos]
  linarith [pi_gt_three]

/-- Product formula: c_n · c_{n+1} = 2/(n·π) for n ≥ 2.
    Proof: direct cancellation using the sphere area recurrence σ(n) = 2π/(n-1)·σ(n-2). -/
theorem cauchyCrofton_product (n : ℕ) (hn : 2 ≤ n) :
    cauchyCroftonConst n * cauchyCroftonConst (n + 1) = 2 / ((n : ℝ) * π) := by
  unfold cauchyCroftonConst
  simp only [show n + 1 - 2 = n - 1 from by omega, show n + 1 - 1 = n from by omega]
  have hpi : (0 : ℝ) < π := pi_pos
  have hσn2 : 0 < sphereArea (n - 2) := sphereArea_pos _
  have hσn1 : 0 < sphereArea (n - 1) := sphereArea_pos _
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by exact_mod_cast Nat.lt_of_lt_pred (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  -- Use recurrence: σ(n) = 2π/(n-1) · σ(n-2)
  have hrec := sphereArea_recurrence n hn
  -- After substituting hrec, the σ(n-2) factors cancel
  rw [hrec]
  field_simp [hpi.ne', hn_pos.ne', hn1.ne', hσn2.ne', hσn1.ne']
  ring

/-- The two-step ratio: c_{n+2}/c_n = n/(n+1) for n ≥ 2.
    Proof: divide the product formulas for (n,n+1) and (n+1,n+2). -/
theorem cauchyCrofton_ratio (n : ℕ) (hn : 2 ≤ n) :
    cauchyCroftonConst (n + 2) * cauchyCroftonConst n = cauchyCroftonConst n ^ 2 * ((n : ℝ) / (n + 1)) := by
  have h1 := cauchyCrofton_product n hn
  have h2 := cauchyCrofton_product (n + 1) (by omega)
  simp only [show n + 1 + 1 = n + 2 from rfl] at h2
  have hcn1_pos : 0 < cauchyCroftonConst (n + 1) := cauchyCroftonConst_pos _ (by omega)
  have hpi : π ≠ 0 := pi_ne_zero
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- h1: c_n * c_{n+1} = 2/(n*π), h2: c_{n+1} * c_{n+2} = 2/((n+1)*π)
  -- Goal: c_{n+2} * c_n = c_n^2 * (n/(n+1))
  -- Equivalently: c_{n+2} * c_{n+1} / (c_n * c_{n+1}) = n/(n+1)
  nlinarith [h1, h2, hcn1_pos, hn_pos, hn1_pos, mul_pos hcn1_pos hn_pos,
             mul_comm (cauchyCroftonConst n) (cauchyCroftonConst (n + 1)),
             mul_comm (cauchyCroftonConst (n + 1)) (cauchyCroftonConst (n + 2)),
             pi_pos]

/-- The Cauchy-Crofton constant decays to zero: c_n → 0 as n → ∞.

    Proof strategy (using cauchyCrofton_product):
    1. c_n · c_{n+1} = 2/(n·π) → 0
    2. c_{n+2}/c_n = n/(n+1) (two-step ratio)
    3. Even subsequence: c_{2k} ≤ c_2/√k (via ∏ 2j/(2j+1) ≤ 1/√k, since 2j/(2j+1) ≤ √(j/(j+1)))
    4. Odd subsequence: similar bound
    5. Squeeze both subsequences to 0

    The bound 2j/(2j+1) ≤ √(j/(j+1)) follows from (2j)^2(j+1) ≤ (2j+1)^2·j,
    which telescopes to give ∏ ≤ √(1/k). -/
theorem cauchyCroftonConst_tendsto_zero :
    Filter.Tendsto cauchyCroftonConst Filter.atTop (nhds 0) := by
  sorry

end CauchyCrofton
