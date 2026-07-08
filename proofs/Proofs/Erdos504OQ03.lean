/-
Erdős Problem #504 — OQ-03: Uniqueness of optimal configurations for the
maximum-angle problem, the N = 3 base case.

Parent problem (Erdős #504, Blumenthal's problem, solved by Sendov 1993):
let α_N be the smallest achievable value of the largest angle determined by N
points in the plane,

    α_N = min_{|P| = N} max_{a,b,c ∈ P} ∠ a b c.

Equivalently α_N is the largest angle that is *always forced*: every N-point
set contains three points spanning an angle ≥ α_N.  Sub-question OQ-03 asks for
which N the optimal (angle-minimising) configuration is unique up to similarity.

This file settles the smallest genuine case, N = 3.  For three pairwise-distinct
points the largest of the three interior angles is always ≥ π/3, and equality
holds *exactly* for the equilateral triangle.  Hence α₃ = π/3 and the extremal
3-point configuration is the equilateral triangle, unique up to similarity — the
base case of the uniqueness question.

Everything is elementary and axiom-free, built on Mathlib's triangle angle-sum
`angle_add_angle_add_angle_eq_pi`, the isosceles-triangle theorem (pons asinorum)
`angle_eq_angle_of_dist_eq`, and its converse
`dist_eq_of_angle_eq_angle_of_angle_ne_pi`.

Main results:
  * `exists_angle_ge_pi_div_three` — some interior angle of any (non-degenerate)
    triangle is ≥ π/3.
  * `maxAngle_ge_pi_div_three` — the maximum interior angle is ≥ π/3, i.e.
    α₃ ≥ π/3.
  * `all_angles_eq_pi_div_three_iff_equilateral` — all three interior angles
    equal π/3 iff the three side lengths are equal.
  * `maxAngle_eq_pi_div_three_iff_equilateral` — the maximum angle equals π/3
    iff the triangle is equilateral.
  * `alpha_three_optimal_iff_equilateral` — capstone: α₃ = π/3 is attained
    exactly by the equilateral triangle (N = 3 uniqueness).
-/

import Mathlib

open Real
open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos504OQ03

open EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- **Some angle of a triangle is at least π/3.**  The three interior angles of a
(non-degenerate) triangle sum to `π`, so at least one of them is ≥ `π/3`. -/
theorem exists_angle_ge_pi_div_three (A B C : P) (h : B ≠ A) :
    π / 3 ≤ ∠ A B C ∨ π / 3 ≤ ∠ B C A ∨ π / 3 ≤ ∠ C A B := by
  have hsum : ∠ A B C + ∠ B C A + ∠ C A B = π :=
    angle_add_angle_add_angle_eq_pi C h
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  linarith

/-- The largest interior angle determined by the three points `A B C`. -/
noncomputable def maxAngle (A B C : P) : ℝ :=
  max (∠ A B C) (max (∠ B C A) (∠ C A B))

/-- **α₃ ≥ π/3.**  The maximum interior angle of any (non-degenerate) triangle is
at least `π/3`: three points always span an angle ≥ `π/3`. -/
theorem maxAngle_ge_pi_div_three (A B C : P) (h : B ≠ A) :
    π / 3 ≤ maxAngle A B C := by
  unfold maxAngle
  rcases exists_angle_ge_pi_div_three A B C h with h1 | h2 | h3
  · exact le_max_of_le_left h1
  · exact le_max_of_le_right (le_max_of_le_left h2)
  · exact le_max_of_le_right (le_max_of_le_right h3)

/-- **All three interior angles equal π/3 iff the triangle is equilateral.**
The forward direction is the converse of pons asinorum (equal base angles force
equal sides); the reverse direction is pons asinorum together with the angle
sum. -/
theorem all_angles_eq_pi_div_three_iff_equilateral (A B C : P) (h : B ≠ A) :
    (∠ A B C = π / 3 ∧ ∠ B C A = π / 3 ∧ ∠ C A B = π / 3) ↔
      (dist A B = dist B C ∧ dist B C = dist C A) := by
  have hne : (π / 3 : ℝ) ≠ π := by
    have := Real.pi_pos; intro hpi; linarith
  constructor
  · -- angles all π/3 ⟹ equilateral (converse pons asinorum)
    rintro ⟨hB, hC, hA⟩
    -- dist A B = dist A C
    have e1 : dist A B = dist A C := by
      apply dist_eq_of_angle_eq_angle_of_angle_ne_pi
      · rw [angle_comm A C B, hB, hC]
      · rw [angle_comm B A C, hA]; exact hne
    -- dist B A = dist B C
    have e2 : dist B A = dist B C := by
      apply dist_eq_of_angle_eq_angle_of_angle_ne_pi
      · rw [angle_comm B A C, hA, hC]
      · rw [hB]; exact hne
    refine ⟨?_, ?_⟩
    · rw [dist_comm A B]; exact e2
    · -- dist B C = dist C A
      have hz : dist A B = dist C A := by rw [dist_comm C A]; exact e1
      have hx : dist A B = dist B C := by rw [dist_comm A B]; exact e2
      exact hx.symm.trans hz
  · -- equilateral ⟹ all angles π/3 (pons asinorum + angle sum)
    rintro ⟨q1, q2⟩
    have hsum : ∠ A B C + ∠ B C A + ∠ C A B = π :=
      angle_add_angle_add_angle_eq_pi C h
    have hAC : dist A B = dist A C := by rw [dist_comm A C, ← q2, ← q1]
    have p1 : ∠ A B C = ∠ A C B := angle_eq_angle_of_dist_eq hAC
    have hBC_eq : ∠ A B C = ∠ B C A := by rw [p1, angle_comm A C B]
    have hBA : dist B A = dist B C := by rw [dist_comm B A]; exact q1
    have p2 : ∠ B A C = ∠ B C A := angle_eq_angle_of_dist_eq hBA
    have hCA_eq : ∠ C A B = ∠ B C A := by rw [← angle_comm B A C]; exact p2
    exact ⟨by linarith, by linarith, by linarith⟩

/-- **N = 3 uniqueness (angle form).**  The maximum interior angle equals its
minimum possible value `π/3` iff the three points form an equilateral triangle. -/
theorem maxAngle_eq_pi_div_three_iff_equilateral (A B C : P) (h : B ≠ A) :
    maxAngle A B C = π / 3 ↔ (dist A B = dist B C ∧ dist B C = dist C A) := by
  constructor
  · intro hmax
    have hsum : ∠ A B C + ∠ B C A + ∠ C A B = π :=
      angle_add_angle_add_angle_eq_pi C h
    have h1 : ∠ A B C ≤ π / 3 := by
      rw [← hmax]; exact le_max_left _ _
    have h2 : ∠ B C A ≤ π / 3 := by
      rw [← hmax]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : ∠ C A B ≤ π / 3 := by
      rw [← hmax]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    refine (all_angles_eq_pi_div_three_iff_equilateral A B C h).mp ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  · intro heq
    obtain ⟨ha1, ha2, ha3⟩ :=
      (all_angles_eq_pi_div_three_iff_equilateral A B C h).mpr heq
    simp only [maxAngle, ha1, ha2, ha3, max_self]

/-- **N = 3 base case of Erdős #504 OQ-03.**  For any three pairwise-distinct
points the largest determined angle is ≥ `π/3`, and this minimum value `π/3` is
attained *exactly* by the equilateral triangle.  Hence `α₃ = π/3` and the
optimal 3-point configuration is unique up to similarity. -/
theorem alpha_three_optimal_iff_equilateral (A B C : P) (h : B ≠ A) :
    π / 3 ≤ maxAngle A B C ∧
      (maxAngle A B C = π / 3 ↔ (dist A B = dist B C ∧ dist B C = dist C A)) :=
  ⟨maxAngle_ge_pi_div_three A B C h, maxAngle_eq_pi_div_three_iff_equilateral A B C h⟩

end Erdos504OQ03
