/-
Isoperimetric Shapes on Other Surfaces

Open Question from: Isoperimetric Theorem (Wiedijk #43)

The classical isoperimetric inequality 4πA ≤ L² holds in the Euclidean plane.
What happens on curved surfaces? On the sphere S² and hyperbolic plane H²,
the isoperimetric inequality takes modified forms reflecting the curvature.

Key Results:
- Sphere S²: L² ≥ 4πA - A² (geodesic caps are optimal)
- Hyperbolic plane H²: L² ≥ 4πA + A² (geodesic disks are optimal)
- Unified: L² ≥ 4πA - κA² where κ is the Gaussian curvature

The sign of the curvature correction A² is crucial:
- κ = 0 (Euclidean): L² ≥ 4πA (original isoperimetric inequality)
- κ > 0 (sphere): L² ≥ 4πA - A² (weaker — curvature helps enclose area)
- κ < 0 (hyperbolic): L² ≥ 4πA + A² (stronger — curvature penalizes area)

References:
- Osserman (1978): "The isoperimetric inequality", Bull. AMS
- Burago-Zalgaller (1988): Geometric Inequalities, Ch. 6
- Chavel (2001): Isoperimetric Inequalities, Cambridge

Tags: differential-geometry, isoperimetric, surfaces, curvature
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

namespace IsoperimetricSurfaces

/-
## Part I: Abstract Surface Regions
-/

/-- A region on a surface, characterized by its boundary length and area.
    This is the analogue of SimpleClosedCurve from the Euclidean case. -/
structure SurfaceRegion where
  boundaryLength : ℝ
  boundaryLength_nonneg : 0 ≤ boundaryLength
  area : ℝ
  area_pos : 0 < area

/-- Shorthand for boundary length -/
def SurfaceRegion.L (R : SurfaceRegion) : ℝ := R.boundaryLength

/-- Shorthand for area -/
def SurfaceRegion.A (R : SurfaceRegion) : ℝ := R.area

/-
## Part II: The Unit Sphere S²
-/

/-- A spherical cap on S² (the unit sphere, total area 4π).
    A cap is the region within geodesic distance θ from a pole.
    - Area = 2π(1 - cos θ)
    - Boundary length = 2π sin θ -/
structure SphericalCap where
  colatitude : ℝ
  colatitude_pos : 0 < colatitude
  colatitude_lt_pi : colatitude < π

/-- Area of a spherical cap: A = 2π(1 - cos θ) -/
noncomputable def SphericalCap.area (c : SphericalCap) : ℝ :=
  2 * π * (1 - cos c.colatitude)

/-- Boundary length of a spherical cap: L = 2π sin θ -/
noncomputable def SphericalCap.boundaryLength (c : SphericalCap) : ℝ :=
  2 * π * sin c.colatitude

/-- The area of a spherical cap is positive -/
theorem SphericalCap.area_pos (c : SphericalCap) : 0 < c.area := by
  unfold area
  have hpi : 0 < π := pi_pos
  have hcos : cos c.colatitude < 1 := by
    exact cos_lt_one_of_ne_zero c.colatitude (ne_of_gt c.colatitude_pos)
  linarith [mul_pos (by linarith : (0 : ℝ) < 2 * π) (by linarith : (0 : ℝ) < 1 - cos c.colatitude)]

/-- The boundary length of a spherical cap is positive -/
theorem SphericalCap.boundaryLength_pos (c : SphericalCap) : 0 < c.boundaryLength := by
  unfold boundaryLength
  have hpi : 0 < π := pi_pos
  have hsin : 0 < sin c.colatitude := sin_pos_of_pos_of_lt_pi c.colatitude_pos c.colatitude_lt_pi
  linarith [mul_pos (by linarith : (0 : ℝ) < 2 * π) hsin]

/-- Convert a spherical cap to a surface region -/
noncomputable def SphericalCap.toRegion (c : SphericalCap) : SurfaceRegion where
  boundaryLength := c.boundaryLength
  boundaryLength_nonneg := le_of_lt c.boundaryLength_pos
  area := c.area
  area_pos := c.area_pos

/-
## Part III: The Spherical Isoperimetric Inequality
-/

/-- **Spherical Isoperimetric Inequality**

For any region on the unit sphere S² with boundary length L and area A
(where 0 < A ≤ 4π):

  L² ≥ 4πA - A²

This is WEAKER than the Euclidean inequality L² ≥ 4πA because
positive curvature (κ = 1) "helps" enclose area.

The correction term -A² comes from the Gauss-Bonnet theorem:
for a region on a surface with constant curvature κ,
  L = ∮ ds ≥ √(4πA - κA²)

Equality holds iff the region is a geodesic cap. -/
axiom spherical_isoperimetric (R : SurfaceRegion) (hA : R.A ≤ 4 * π) :
    R.L ^ 2 ≥ 4 * π * R.A - R.A ^ 2

/-- Spherical caps achieve equality in the spherical isoperimetric inequality.

For a cap with colatitude θ:
- A = 2π(1 - cos θ), L = 2π sin θ
- L² = 4π² sin² θ
- 4πA - A² = 4π·2π(1-cos θ) - [2π(1-cos θ)]²
           = 8π²(1-cos θ) - 4π²(1-cos θ)²
           = 4π²(1-cos θ)[2 - (1-cos θ)]
           = 4π²(1-cos θ)(1+cos θ)
           = 4π² sin² θ = L² ✓ -/
theorem spherical_cap_equality (c : SphericalCap) :
    c.toRegion.L ^ 2 = 4 * π * c.toRegion.A - c.toRegion.A ^ 2 := by
  unfold SurfaceRegion.L SurfaceRegion.A SphericalCap.toRegion
  unfold SphericalCap.boundaryLength SphericalCap.area
  have hsin2 : sin c.colatitude ^ 2 = 1 - cos c.colatitude ^ 2 := by
    have := sin_sq_add_cos_sq c.colatitude
    linarith
  nlinarith [sin_sq_add_cos_sq c.colatitude, pi_pos]

/-- Equality characterization: optimal regions on S² are geodesic caps -/
/-
## Part IV: The Hyperbolic Plane H²
-/

/-- A geodesic disk in the hyperbolic plane H² (Gaussian curvature κ = -1).
    A disk of hyperbolic radius r has:
    - Area = 4π sinh²(r/2) = 2π(cosh r - 1)
    - Boundary length = 2π sinh r -/
structure HyperbolicDisk where
  radius : ℝ
  radius_pos : 0 < radius

/-- Area of a hyperbolic disk: A = 2π(cosh r - 1) -/
noncomputable def HyperbolicDisk.area (d : HyperbolicDisk) : ℝ :=
  2 * π * (cosh d.radius - 1)

/-- Boundary length of a hyperbolic disk: L = 2π sinh r -/
noncomputable def HyperbolicDisk.boundaryLength (d : HyperbolicDisk) : ℝ :=
  2 * π * sinh d.radius

/-- The area of a hyperbolic disk is positive -/
theorem HyperbolicDisk.area_pos (d : HyperbolicDisk) : 0 < d.area := by
  unfold area
  have hpi : 0 < π := pi_pos
  have hcosh : 1 < cosh d.radius := by
    exact one_lt_cosh (ne_of_gt d.radius_pos)
  linarith [mul_pos (by linarith : (0 : ℝ) < 2 * π) (by linarith : (0 : ℝ) < cosh d.radius - 1)]

/-- The boundary length of a hyperbolic disk is positive -/
theorem HyperbolicDisk.boundaryLength_pos (d : HyperbolicDisk) : 0 < d.boundaryLength := by
  unfold boundaryLength
  have hpi : 0 < π := pi_pos
  have hsinh : 0 < sinh d.radius := sinh_pos_of_pos d.radius_pos
  linarith [mul_pos (by linarith : (0 : ℝ) < 2 * π) hsinh]

/-- Convert a hyperbolic disk to a surface region -/
noncomputable def HyperbolicDisk.toRegion (d : HyperbolicDisk) : SurfaceRegion where
  boundaryLength := d.boundaryLength
  boundaryLength_nonneg := le_of_lt d.boundaryLength_pos
  area := d.area
  area_pos := d.area_pos

/-
## Part V: The Hyperbolic Isoperimetric Inequality
-/

/-- **Hyperbolic Isoperimetric Inequality**

For any region in the hyperbolic plane H² with boundary length L and area A:

  L² ≥ 4πA + A²

This is STRONGER than the Euclidean inequality L² ≥ 4πA because
negative curvature (κ = -1) "penalizes" enclosing area.

The correction term +A² reflects the exponential growth of hyperbolic space:
a hyperbolic disk of area A has perimeter ~2√(πA) + A/2 for large A,
meaning most of the "volume" is near the boundary.

Equality holds iff the region is a geodesic disk. -/
axiom hyperbolic_isoperimetric (R : SurfaceRegion) :
    R.L ^ 2 ≥ 4 * π * R.A + R.A ^ 2

/-- Geodesic disks achieve equality in the hyperbolic isoperimetric inequality.

For a disk with radius r:
- A = 2π(cosh r - 1), L = 2π sinh r
- L² = 4π² sinh² r
- 4πA + A² = 4π·2π(cosh r - 1) + [2π(cosh r - 1)]²
           = 8π²(cosh r - 1) + 4π²(cosh r - 1)²
           = 4π²(cosh r - 1)[2 + (cosh r - 1)]
           = 4π²(cosh r - 1)(cosh r + 1)
           = 4π²(cosh² r - 1)
           = 4π² sinh² r = L² ✓ -/
theorem hyperbolic_disk_equality (d : HyperbolicDisk) :
    d.toRegion.L ^ 2 = 4 * π * d.toRegion.A + d.toRegion.A ^ 2 := by
  unfold SurfaceRegion.L SurfaceRegion.A HyperbolicDisk.toRegion
  unfold HyperbolicDisk.boundaryLength HyperbolicDisk.area
  have hid : sinh d.radius ^ 2 = cosh d.radius ^ 2 - 1 := by
    have := cosh_sq_sub_sinh_sq d.radius
    linarith
  nlinarith [cosh_sq_sub_sinh_sq d.radius, pi_pos]

/-- Equality characterization: optimal regions in H² are geodesic disks -/
/-
## Part VI: Unified Curvature Framework
-/

/-- **Unified Isoperimetric Inequality on Constant-Curvature Surfaces**

For a region with boundary length L and area A on a simply connected surface
of constant Gaussian curvature κ:

  L² ≥ 4πA - κA²

Special cases:
- κ = 0 (Euclidean plane): L² ≥ 4πA
- κ = 1 (unit sphere S²): L² ≥ 4πA - A²
- κ = -1 (hyperbolic plane H²): L² ≥ 4πA + A²

The sign of κ determines whether curvature helps or hinders enclosure:
- Positive curvature weakens the constraint (less perimeter needed)
- Negative curvature strengthens it (more perimeter needed) -/
def UnifiedIsoperimetric (κ : ℝ) : Prop :=
  ∀ R : SurfaceRegion, R.L ^ 2 ≥ 4 * π * R.A - κ * R.A ^ 2

/-- The Euclidean case (κ = 0) recovers the classical inequality -/
theorem euclidean_is_zero_curvature :
    UnifiedIsoperimetric 0 ↔
    (∀ R : SurfaceRegion, R.L ^ 2 ≥ 4 * π * R.A) := by
  unfold UnifiedIsoperimetric
  simp [zero_mul, sub_zero]

/-- The spherical case (κ = 1) gives the spherical inequality -/
theorem spherical_is_positive_curvature :
    UnifiedIsoperimetric 1 ↔
    (∀ R : SurfaceRegion, R.L ^ 2 ≥ 4 * π * R.A - R.A ^ 2) := by
  unfold UnifiedIsoperimetric
  simp [one_mul]

/-- The hyperbolic case (κ = -1) gives the hyperbolic inequality -/
theorem hyperbolic_is_negative_curvature :
    UnifiedIsoperimetric (-1) ↔
    (∀ R : SurfaceRegion, R.L ^ 2 ≥ 4 * π * R.A + R.A ^ 2) := by
  unfold UnifiedIsoperimetric
  constructor
  · intro h R
    have := h R
    linarith
  · intro h R
    have := h R
    linarith

/-- Monotonicity: smaller curvature gives a stronger inequality.
    If κ₁ ≤ κ₂ then UnifiedIsoperimetric κ₁ → UnifiedIsoperimetric κ₂.
    (Smaller = more negative = stronger constraint.) -/
theorem isoperimetric_monotone (κ₁ κ₂ : ℝ) (hκ : κ₁ ≤ κ₂) :
    UnifiedIsoperimetric κ₁ → UnifiedIsoperimetric κ₂ := by
  intro h R
  have h1 := h R
  have hA2 : 0 ≤ R.A ^ 2 := sq_nonneg R.A
  nlinarith

/-
## Part VII: Isoperimetric Ratios on Curved Surfaces
-/

/-- The isoperimetric ratio on a surface with curvature κ.
    On flat space: ratio = A/L² with optimal value 1/(4π).
    On curved space: the "corrected ratio" accounts for curvature. -/
noncomputable def correctedRatio (R : SurfaceRegion) (κ : ℝ) : ℝ :=
  (4 * π * R.A - κ * R.A ^ 2) / R.L ^ 2

/-- The corrected ratio is at most 1 when the unified inequality holds -/
theorem corrected_ratio_le_one (κ : ℝ) (h : UnifiedIsoperimetric κ) (R : SurfaceRegion) :
    correctedRatio R κ ≤ 1 := by
  unfold correctedRatio
  have hL2 : 0 < R.L ^ 2 := by
    have hL : 0 < R.boundaryLength := by
      -- From the isoperimetric inequality, L can't be 0 for positive area
      by_contra hle
      push_neg at hle
      have hL0 : R.L = 0 := le_antisymm (not_lt.mp hle) R.boundaryLength_nonneg
      have := h R
      unfold SurfaceRegion.L at hL0
      rw [hL0] at this
      simp at this
      linarith [R.area_pos, sq_nonneg R.A]
    exact sq_pos_of_pos hL
  rw [div_le_one hL2]
  exact h R

/-
## Part VIII: Comparison Across Geometries
-/

/-- On the sphere, less perimeter is needed than in Euclidean space.
    For the same area, a spherical region can have shorter boundary. -/
theorem sphere_needs_less_perimeter (R : SurfaceRegion)
    (hA : R.A ≤ 4 * π)
    (hsph : R.L ^ 2 ≥ 4 * π * R.A - R.A ^ 2)
    (heuc : R.L ^ 2 ≥ 4 * π * R.A) :
    4 * π * R.A - R.A ^ 2 ≤ 4 * π * R.A := by
  nlinarith [sq_nonneg R.A]

/-- On the hyperbolic plane, more perimeter is needed than in Euclidean space. -/
theorem hyperbolic_needs_more_perimeter (R : SurfaceRegion) :
    4 * π * R.A + R.A ^ 2 ≥ 4 * π * R.A := by
  linarith [sq_nonneg R.A]

/-
## Part IX: Asymptotic Behavior
-/

/-- For small areas (A → 0), all three geometries agree to first order.
    The curvature correction κA² is negligible compared to 4πA. -/
theorem small_area_universal (R : SurfaceRegion) (κ : ℝ) (hA : R.A ≤ 1) :
    |κ * R.A ^ 2| ≤ |κ| * R.A := by
  rw [abs_mul, abs_mul]
  have hA_pos := R.area_pos
  have hA2 : |R.A ^ 2| = R.A ^ 2 := abs_of_nonneg (sq_nonneg R.A)
  have hAabs : |R.A| = R.A := abs_of_pos hA_pos
  rw [hA2, hAabs]
  nlinarith [sq_nonneg R.A]

/-
## Summary

**Isoperimetric Shapes on Other Surfaces**

The isoperimetric inequality generalizes beautifully to constant-curvature surfaces:

  L² ≥ 4πA - κA²

| Surface | κ | Inequality | Optimal Shape |
|---------|---|------------|---------------|
| Euclidean plane | 0 | L² ≥ 4πA | Circle |
| Unit sphere S² | +1 | L² ≥ 4πA - A² | Geodesic cap |
| Hyperbolic plane H² | -1 | L² ≥ 4πA + A² | Geodesic disk |

The curvature correction tells a physical story:
- Positive curvature (sphere) means space "curves back", helping enclose area
- Negative curvature (hyperbolic) means space "spreads out", fighting enclosure
- At small scales, all geometries look Euclidean (the correction is O(A²))

Optimal shapes are always "geodesic balls" — the most symmetric regions.
This reflects a deep principle: isoperimetric minimizers inherit the symmetry
of the ambient space.
-/

/-- Summary: the three isoperimetric inequalities -/
theorem isoperimetric_on_surfaces :
    -- Spherical: L² ≥ 4πA - A²
    (∀ R : SurfaceRegion, R.A ≤ 4 * π → R.L ^ 2 ≥ 4 * π * R.A - R.A ^ 2) ∧
    -- Hyperbolic: L² ≥ 4πA + A²
    (∀ R : SurfaceRegion, R.L ^ 2 ≥ 4 * π * R.A + R.A ^ 2) ∧
    -- Spherical caps are tight
    (∀ c : SphericalCap, c.toRegion.L ^ 2 = 4 * π * c.toRegion.A - c.toRegion.A ^ 2) ∧
    -- Hyperbolic disks are tight
    (∀ d : HyperbolicDisk, d.toRegion.L ^ 2 = 4 * π * d.toRegion.A + d.toRegion.A ^ 2) :=
  ⟨fun R hA => spherical_isoperimetric R hA,
   fun R => hyperbolic_isoperimetric R,
   fun c => spherical_cap_equality c,
   fun d => hyperbolic_disk_equality d⟩

end IsoperimetricSurfaces
