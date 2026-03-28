/-
Erdős Problem #352: Triangles of Area 1 in Measurable Sets

**Question**: Is there some c > 0 such that every measurable A ⊆ ℝ² of measure ≥ c
contains the vertices of a triangle of area 1?

**Status**: OPEN

**Known Results**:
- Erdős (unpublished): TRUE if A has infinite measure
- Erdős (unpublished): TRUE if A is unbounded with positive measure
  (Both follow "easily from the Lebesgue density theorem")
- Conjectured threshold: c = 4π/√27 ≈ 2.418
- Freiling-Mauldin (2002): If outer measure > 4π/√27, then A contains
  triangle with area > 1 (proves conjecture for compact convex sets)
- Problem reduces to unions of finitely many compact convex interiors
- Freiling-Mauldin proved for n ≤ 3 such sets

**The Conjectured Constant**:
c = 4π/√27 is witnessed by a circle of radius < 2·3^{-3/4}.
Any circle of this radius has area exactly 4π/√27 but contains no
triangle of area 1 (the largest inscribed triangle is equilateral
with area 3√3/4·r² < 1).

References:
- https://erdosproblems.com/352
- [Er78d] Erdős, "Set-theoretic, measure-theoretic, combinatorial..." (1978/79)
- [Er83d] Erdős, "Some combinatorial, geometric and set theoretic problems..." (1984)
- [Ma02] Mauldin, "Some problems in set theory, analysis and geometry" (2002)
- [Ma13] Mauldin, "Some problems and ideas of Erdős in analysis and geometry" (2013)
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Erdos352

open MeasureTheory Set

/- ## Triangle Area in ℝ²

The area of a triangle with vertices p, q, r in ℝ² is given by:
  Area = (1/2)|det([q-p, r-p])| = (1/2)|((q-p)×(r-p))|

where × denotes the 2D cross product (a scalar in 2D).
-/

/-- The 2D cross product (wedge product), giving a scalar.
For vectors u = (u₁, u₂) and v = (v₁, v₂): u × v = u₁v₂ - u₂v₁ -/
def cross2D (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The signed area of triangle with vertices p, q, r.
Positive if p, q, r are counterclockwise. -/
noncomputable def signedTriangleArea (p q r : ℝ × ℝ) : ℝ :=
  cross2D (q.1 - p.1, q.2 - p.2) (r.1 - p.1, r.2 - p.2) / 2

/-- The (unsigned) area of a triangle with vertices p, q, r. -/
noncomputable def triangleArea (p q r : ℝ × ℝ) : ℝ := |signedTriangleArea p q r|

/- ## Basic Properties of Triangle Area -/

/-- Cross product is antisymmetric. -/
theorem cross2D_antisymm (u v : ℝ × ℝ) : cross2D u v = -cross2D v u := by
  simp only [cross2D]
  ring

/-- Triangle area is symmetric under vertex permutation.
Axiomatized due to detailed algebra with absolute values. -/

/- ## The Main Property

A set A ⊆ ℝ² "contains a unit triangle" if there exist three points in A
forming a triangle of area exactly 1. -/

/-- A set contains the vertices of a triangle with area a. -/
def ContainsTriangleOfArea (A : Set (ℝ × ℝ)) (a : ℝ) : Prop :=
  ∃ p q r : ℝ × ℝ, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧ triangleArea p q r = a

/-- A set contains a unit triangle (area = 1). -/
def ContainsUnitTriangle (A : Set (ℝ × ℝ)) : Prop := ContainsTriangleOfArea A 1

/- ## The Main Question -/

/-- **Erdős Problem #352 (OPEN)**:

Is there c > 0 such that every measurable A ⊆ ℝ² with measure ≥ c
contains a unit triangle?

This is axiomatized as an unknown Prop since the answer is not known. -/

/-- The formal statement of the main question. -/
def erdos_352_statement : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Set (ℝ × ℝ), MeasurableSet A →
      volume A ≥ ENNReal.ofReal c → ContainsUnitTriangle A

/- ## The Conjectured Constant

Erdős conjectured c = 4π/√27 ≈ 2.418, witnessed by a circle of radius < 2·3^{-3/4}.
-/

/-- The conjectured optimal constant: 4π/√27. -/
noncomputable def erdosConstant : ℝ := 4 * Real.pi / Real.sqrt 27

/-- Numerical approximation: 4π/√27 ≈ 2.418. -/
theorem erdosConstant_approx : erdosConstant > 2.4 ∧ erdosConstant < 2.5 := by
  unfold erdosConstant
  have hsqrt_pos : 0 < Real.sqrt 27 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt_lt : Real.sqrt 27 < 5.197 := by
    rw [show (5.197 : ℝ) = Real.sqrt (5.197 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5.197)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsqrt_gt : 5.196 < Real.sqrt 27 := by
    rw [show (5.196 : ℝ) = Real.sqrt (5.196 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5.196)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor
  · rw [gt_iff_lt, lt_div_iff hsqrt_pos]
    linarith [Real.pi_gt_314]
  · rw [div_lt_iff hsqrt_pos]
    linarith [Real.pi_lt_315]

/-- The conjectured statement: c = 4π/√27 suffices. -/
def erdos_352_conjecture : Prop :=
  ∀ A : Set (ℝ × ℝ), MeasurableSet A →
    volume A ≥ ENNReal.ofReal erdosConstant → ContainsUnitTriangle A

/-- The conjecture that 4π/√27 is optimal (a circle of critical radius shows this). -/
def erdos_352_optimal : Prop :=
  ∀ ε > 0, ∃ A : Set (ℝ × ℝ), MeasurableSet A ∧
    volume A ≥ ENNReal.ofReal (erdosConstant - ε) ∧
    ¬ContainsUnitTriangle A

/- ## Known Results -/

/-- **Erdős (unpublished)**: Sets of infinite measure contain unit triangles.
Follows from the Lebesgue density theorem. -/

/-- **Erdős (unpublished)**: Unbounded sets of positive measure contain unit triangles.
Also follows from the Lebesgue density theorem. -/

/-- **Freiling-Mauldin (2002)**: If outer measure > 4π/√27, then A contains
a triangle with area > 1 (not just = 1). -/

/- ## The Witness: Critical Circle

A circle of radius r = 2·3^{-3/4} has area exactly 4π/√27 but the largest
inscribed triangle is equilateral with area 3√3/4·r² = √3·3^{-1/2} < 1.
-/

/-- The critical radius: r = 2·3^{-3/4} ≈ 0.877 -/
noncomputable def criticalRadius : ℝ := 2 * (3 : ℝ) ^ (-(3/4 : ℝ))

/-- A circle of the critical radius has area exactly 4π/√27. -/
theorem critical_circle_area : Real.pi * criticalRadius ^ 2 = erdosConstant := by
  simp only [criticalRadius, erdosConstant]
  have h3_pos : (0 : ℝ) < 3 := by norm_num
  have h3_nn : (0 : ℝ) ≤ 3 := by norm_num
  -- (2 * 3^(-3/4))^2 = 4 * 3^(-3/2)
  rw [mul_pow, show (2 : ℝ) ^ 2 = 4 from by norm_num]
  have h_cr_sq : ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ 2 = (3 : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [sq, ← Real.rpow_add h3_pos]; congr 1; norm_num
  rw [h_cr_sq]
  -- √27 = 3^(3/2)
  have h_sqrt27 : Real.sqrt 27 = (3 : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, show (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) from by norm_num,
        ← Real.rpow_natCast (3 : ℝ) 3, ← Real.rpow_mul h3_nn]
    congr 1; norm_num
  -- 3^(-3/2) = (√27)⁻¹
  have h_inv : (3 : ℝ) ^ (-(3 / 2 : ℝ)) = (Real.sqrt 27)⁻¹ := by
    conv_rhs => rw [h_sqrt27]
    rw [Real.rpow_neg h3_nn]
  rw [h_inv, div_eq_mul_inv]
  ring

/-- The largest triangle inscribed in a circle of radius r is equilateral
with area (3√3/4)r². For the critical radius, this equals exactly 1.
This shows the critical circle is the exact boundary case: the optimality
of 4π/√27 follows because circles of radius strictly less than
criticalRadius have max inscribed triangle area strictly less than 1. -/
theorem critical_circle_max_area :
    3 * Real.sqrt 3 / 4 * criticalRadius ^ 2 = 1 := by
  simp only [criticalRadius]
  have h3_pos : (0 : ℝ) < 3 := by norm_num
  have h3_nn : (0 : ℝ) ≤ 3 := by norm_num
  rw [mul_pow, show (2 : ℝ) ^ 2 = 4 from by norm_num]
  have h_sq : ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ 2 = (3 : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [sq, ← Real.rpow_add h3_pos]; congr 1; norm_num
  rw [h_sq, Real.sqrt_eq_rpow]
  -- 3 * 3^(1/2) / 4 * (4 * 3^(-3/2)) = 3 * (3^(1/2) * 3^(-3/2)) = 3 * 3^(-1) = 1
  have h_ring : (3 : ℝ) * (3 : ℝ) ^ ((1 : ℝ) / 2) / 4 * (4 * (3 : ℝ) ^ (-(3 / 2 : ℝ))) =
                3 * ((3 : ℝ) ^ ((1 : ℝ) / 2) * (3 : ℝ) ^ (-(3 / 2 : ℝ))) := by ring
  rw [h_ring, ← Real.rpow_add h3_pos]
  have h_exp : (1 : ℝ) / 2 + -(3 / 2 : ℝ) = -(1 : ℝ) := by norm_num
  rw [h_exp, Real.rpow_neg h3_nn, Real.rpow_one]
  exact mul_inv_cancel₀ (by norm_num)

/- ## Reduction to Finite Unions

Mauldin noted the problem reduces to showing the result for
unions of finitely many compact convex interiors. -/

/-- **Mauldin (2013)**: It suffices to prove the conjecture for sets that are
unions of interiors of finitely many compact convex sets. -/

/-- **Freiling-Mauldin**: The conjecture holds for unions of at most 3
compact convex interiors. -/

/- ## Summary -/

/-- **Erdős Problem #352 Summary**:

1. QUESTION: Does c > 0 exist such that measure ≥ c implies unit triangle exists?
2. STATUS: OPEN
3. CONJECTURE: c = 4π/√27 ≈ 2.418 (witnessed by critical circle)
4. KNOWN: TRUE for infinite measure, unbounded positive measure
5. KNOWN: TRUE for compact convex sets (Freiling-Mauldin 2002)
6. REDUCTION: Suffices to prove for unions of finitely many compact convex interiors
7. PARTIAL: TRUE for unions of ≤ 3 such sets
-/
theorem erdos_352_summary :
    -- The conjectured constant exists and is positive
    erdosConstant > 0 ∧
    -- The area formula is well-defined (example)
    triangleArea (0, 0) (2, 0) (1, 1) = 1 := by
  constructor
  · simp only [erdosConstant]
    positivity
  · simp only [triangleArea, signedTriangleArea, cross2D]
    norm_num

end Erdos352
