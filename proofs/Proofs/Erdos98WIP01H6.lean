/-
  Erdős Problem #98 — first nontrivial upper bound for `h 6`:
  an explicit six-point general-position configuration with only four
  distinct distances, giving `h 6 ≤ 4` and pinning `3 ≤ h 6 ≤ 4`.

  Source: https://erdosproblems.com/98
  Parent: `Proofs/Erdos98WIP01.lean` (defines `h`, `numDistinctDistances`,
  `InGeneralPosition`, proves `h 5 = 3` and the extremal-witness bound
  `h_le_of_inGeneralPosition`) and `Proofs/Erdos98WIP01Thresholds.lean`
  (`three_le_h_six`, the best previously known lower bound for `h 6`).

  The configuration lives on the triangular (Eisenstein) lattice: the six
  lattice points `(0,1), (0,2), (1,3), (2,0), (2,2), (3,0)` in coordinates
  `(a,b) ↦ (a + b/2, b·√3/2)`, i.e. the planar points

    P₀=(1/2, √3/2), P₁=(1, √3), P₂=(5/2, 3√3/2), P₃=(2, 0), P₄=(3, √3), P₅=(3, 0).

  Pairwise squared distances take exactly the four values `{1, 3, 4, 7}`
  (Loeschian values `a² + ab + b²`), so the distances are `{1, √3, 2, √7}`:

    d² = 1 : P₀P₁, P₂P₄, P₃P₅            (3 pairs)
    d² = 3 : P₀P₃, P₁P₂, P₄P₅            (3 pairs)
    d² = 4 : P₁P₃, P₁P₄, P₃P₄            (3 pairs)
    d² = 7 : P₀P₂, P₀P₄, P₀P₅, P₁P₅, P₂P₃, P₂P₅   (6 pairs)

  General position was machine-verified exactly (sympy) before formalization:
  all 20 triples have nonzero signed area, and all 15 quadruples have nonzero
  circumscribed-circle determinant (each a nonzero rational multiple of √3).

  Prior state of the pin: `3 ≤ h 6` (`three_le_h_six`) with only the generic
  ceiling `h 6 ≤ 15` (`h_le_choose_two`).  This file tightens it to
  `3 ≤ h 6 ≤ 4`.  Whether `h 6 = 3` (a six-point general-position three-distance
  set) or `h 6 = 4` remains open here.

  All results are axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/

import Mathlib
import Proofs.Erdos98WIP01
import Proofs.Erdos98WIP01Thresholds

open Finset

namespace Erdos98WIP01

/-- The explicit six-point triangular-lattice configuration
`P₀=(1/2, √3/2)`, `P₁=(1, √3)`, `P₂=(5/2, 3√3/2)`, `P₃=(2, 0)`, `P₄=(3, √3)`,
`P₅=(3, 0)` — a four-distance set (`1, √3, 2, √7`) in general position. -/
noncomputable def h6Config : PointConfig 6 :=
  ![!₂[1 / 2, Real.sqrt 3 / 2], !₂[1, Real.sqrt 3], !₂[5 / 2, 3 * Real.sqrt 3 / 2], !₂[2, 0], !₂[3, Real.sqrt 3], !₂[3, 0]]

set_option maxHeartbeats 3200000 in
/-- **Every pairwise squared distance of `h6Config` is `1`, `3`, `4`, or `7`.**
A direct coordinate computation over all off-diagonal pairs, using `√3² = 3`. -/
theorem h6Config_dist_sq {i j : Fin 6} (hij : i ≠ j) :
    dist (h6Config i) (h6Config j) ^ 2 = 1 ∨
    dist (h6Config i) (h6Config j) ^ 2 = 3 ∨
    dist (h6Config i) (h6Config j) ^ 2 = 4 ∨
    dist (h6Config i) (h6Config j) ^ 2 = 7 := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [EuclideanSpace.dist_sq_eq]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (simp only [h6Config, Fin.sum_univ_two, Real.dist_eq, sq_abs]
       first
       | (left; norm_num [hs2] <;> nlinarith [hs2])
       | (right; left; norm_num [hs2] <;> nlinarith [hs2])
       | (right; right; left; norm_num [hs2] <;> nlinarith [hs2])
       | (right; right; right; norm_num [hs2] <;> nlinarith [hs2]))

/-- **Every pairwise distance of `h6Config` lies in `{1, √3, 2, √7}`.** The
nonnegative square root of `h6Config_dist_sq`. -/
theorem h6Config_dist_mem {i j : Fin 6} (hij : i ≠ j) :
    dist (h6Config i) (h6Config j) ∈
      ({1, Real.sqrt 3, 2, Real.sqrt 7} : Finset ℝ) := by
  have hd0 : 0 ≤ dist (h6Config i) (h6Config j) := dist_nonneg
  rcases h6Config_dist_sq hij with h | h | h | h
  · have he : dist (h6Config i) (h6Config j) = 1 := by
      rw [← Real.sqrt_sq hd0, h, Real.sqrt_one]
    simp [he]
  · have he : dist (h6Config i) (h6Config j) = Real.sqrt 3 := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]
  · have he : dist (h6Config i) (h6Config j) = 2 := by
      rw [← Real.sqrt_sq hd0, h, show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    simp [he]
  · have he : dist (h6Config i) (h6Config j) = Real.sqrt 7 := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]

/-- The six points are distinct: every pairwise distance lies in
`{1, √3, 2, √7}`, all of whose elements are positive. -/
theorem h6Config_injective : Function.Injective h6Config := by
  intro i j hij
  by_contra hne
  have hmem := h6Config_dist_mem hne
  rw [hij, dist_self] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs7 : (0 : ℝ) < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)
  rcases hmem with h | h | h | h
  · norm_num at h
  · linarith [hs3]
  · norm_num at h
  · linarith [hs7]

set_option maxHeartbeats 3200000 in
/-- **No three of the six points are collinear.** A line through any three
forces `(a,b,c) = 0`; verified over all triples (nonzero signed areas). -/
theorem noThreeCollinear_h6Config : NoThreeCollinear h6Config := by
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  intro i j k hcard
  rintro ⟨a, b, c, hne, hi, hj, hk⟩
  apply hne
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | (simp only [h6Config] at hi hj hk
       norm_num at hi hj hk
       simp only [Prod.mk.injEq]
       refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hs, hs2, hi, hj, hk])

/-- No centre is equidistant from `P0, P1, P2, P3`. -/
theorem h6_not_equidistant_0123 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h1 : dist center (h6Config 1) = r) (h2 : dist center (h6Config 2) = r) (h3 : dist center (h6Config 3) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (h6Config 0) ^ 2 = dist center (h6Config 1) ^ 2 := by rw [h0, h1]
  have e02 : dist center (h6Config 0) ^ 2 = dist center (h6Config 2) ^ 2 := by rw [h0, h2]
  have e03 : dist center (h6Config 0) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h0, h3]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e01 e02 e03
  norm_num at e01 e02 e03
  nlinarith [e01, e02, e03, hs2]

/-- No centre is equidistant from `P0, P1, P2, P4`. -/
theorem h6_not_equidistant_0124 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h1 : dist center (h6Config 1) = r) (h2 : dist center (h6Config 2) = r) (h4 : dist center (h6Config 4) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (h6Config 0) ^ 2 = dist center (h6Config 1) ^ 2 := by rw [h0, h1]
  have e02 : dist center (h6Config 0) ^ 2 = dist center (h6Config 2) ^ 2 := by rw [h0, h2]
  have e04 : dist center (h6Config 0) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h0, h4]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e01 e02 e04
  norm_num at e01 e02 e04
  nlinarith [e01, e02, e04, hs2]

/-- No centre is equidistant from `P0, P1, P2, P5`. -/
theorem h6_not_equidistant_0125 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h1 : dist center (h6Config 1) = r) (h2 : dist center (h6Config 2) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (h6Config 0) ^ 2 = dist center (h6Config 1) ^ 2 := by rw [h0, h1]
  have e02 : dist center (h6Config 0) ^ 2 = dist center (h6Config 2) ^ 2 := by rw [h0, h2]
  have e05 : dist center (h6Config 0) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h0, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e01 e02 e05
  norm_num at e01 e02 e05
  nlinarith [e01, e02, e05, hs2]

/-- No centre is equidistant from `P0, P1, P3, P4`. -/
theorem h6_not_equidistant_0134 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h1 : dist center (h6Config 1) = r) (h3 : dist center (h6Config 3) = r) (h4 : dist center (h6Config 4) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (h6Config 0) ^ 2 = dist center (h6Config 1) ^ 2 := by rw [h0, h1]
  have e03 : dist center (h6Config 0) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h0, h3]
  have e04 : dist center (h6Config 0) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h0, h4]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e01 e03 e04
  norm_num at e01 e03 e04
  nlinarith [e01, e03, e04, hs2]

/-- No centre is equidistant from `P0, P1, P3, P5`. -/
theorem h6_not_equidistant_0135 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h1 : dist center (h6Config 1) = r) (h3 : dist center (h6Config 3) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (h6Config 0) ^ 2 = dist center (h6Config 1) ^ 2 := by rw [h0, h1]
  have e03 : dist center (h6Config 0) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h0, h3]
  have e05 : dist center (h6Config 0) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h0, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e01 e03 e05
  norm_num at e01 e03 e05
  nlinarith [e01, e03, e05, hs2]

/-- No centre is equidistant from `P0, P1, P4, P5`. -/
theorem h6_not_equidistant_0145 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h1 : dist center (h6Config 1) = r) (h4 : dist center (h6Config 4) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (h6Config 0) ^ 2 = dist center (h6Config 1) ^ 2 := by rw [h0, h1]
  have e04 : dist center (h6Config 0) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h0, h4]
  have e05 : dist center (h6Config 0) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h0, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e01 e04 e05
  norm_num at e01 e04 e05
  nlinarith [e01, e04, e05, hs2]

/-- No centre is equidistant from `P0, P2, P3, P4`. -/
theorem h6_not_equidistant_0234 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h2 : dist center (h6Config 2) = r) (h3 : dist center (h6Config 3) = r) (h4 : dist center (h6Config 4) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e02 : dist center (h6Config 0) ^ 2 = dist center (h6Config 2) ^ 2 := by rw [h0, h2]
  have e03 : dist center (h6Config 0) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h0, h3]
  have e04 : dist center (h6Config 0) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h0, h4]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e02 e03 e04
  norm_num at e02 e03 e04
  nlinarith [e02, e03, e04, hs2]

/-- No centre is equidistant from `P0, P2, P3, P5`. -/
theorem h6_not_equidistant_0235 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h2 : dist center (h6Config 2) = r) (h3 : dist center (h6Config 3) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e02 : dist center (h6Config 0) ^ 2 = dist center (h6Config 2) ^ 2 := by rw [h0, h2]
  have e03 : dist center (h6Config 0) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h0, h3]
  have e05 : dist center (h6Config 0) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h0, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e02 e03 e05
  norm_num at e02 e03 e05
  nlinarith [e02, e03, e05, hs2]

/-- No centre is equidistant from `P0, P2, P4, P5`. -/
theorem h6_not_equidistant_0245 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h2 : dist center (h6Config 2) = r) (h4 : dist center (h6Config 4) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e02 : dist center (h6Config 0) ^ 2 = dist center (h6Config 2) ^ 2 := by rw [h0, h2]
  have e04 : dist center (h6Config 0) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h0, h4]
  have e05 : dist center (h6Config 0) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h0, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e02 e04 e05
  norm_num at e02 e04 e05
  nlinarith [e02, e04, e05, hs2]

/-- No centre is equidistant from `P0, P3, P4, P5`. -/
theorem h6_not_equidistant_0345 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h6Config 0) = r) (h3 : dist center (h6Config 3) = r) (h4 : dist center (h6Config 4) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e03 : dist center (h6Config 0) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h0, h3]
  have e04 : dist center (h6Config 0) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h0, h4]
  have e05 : dist center (h6Config 0) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h0, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e03 e04 e05
  norm_num at e03 e04 e05
  nlinarith [e03, e04, e05, hs2]

/-- No centre is equidistant from `P1, P2, P3, P4`. -/
theorem h6_not_equidistant_1234 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h1 : dist center (h6Config 1) = r) (h2 : dist center (h6Config 2) = r) (h3 : dist center (h6Config 3) = r) (h4 : dist center (h6Config 4) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e12 : dist center (h6Config 1) ^ 2 = dist center (h6Config 2) ^ 2 := by rw [h1, h2]
  have e13 : dist center (h6Config 1) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h1, h3]
  have e14 : dist center (h6Config 1) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h1, h4]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e12 e13 e14
  norm_num at e12 e13 e14
  nlinarith [e12, e13, e14, hs2]

/-- No centre is equidistant from `P1, P2, P3, P5`. -/
theorem h6_not_equidistant_1235 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h1 : dist center (h6Config 1) = r) (h2 : dist center (h6Config 2) = r) (h3 : dist center (h6Config 3) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e12 : dist center (h6Config 1) ^ 2 = dist center (h6Config 2) ^ 2 := by rw [h1, h2]
  have e13 : dist center (h6Config 1) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h1, h3]
  have e15 : dist center (h6Config 1) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h1, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e12 e13 e15
  norm_num at e12 e13 e15
  nlinarith [e12, e13, e15, hs2]

/-- No centre is equidistant from `P1, P2, P4, P5`. -/
theorem h6_not_equidistant_1245 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h1 : dist center (h6Config 1) = r) (h2 : dist center (h6Config 2) = r) (h4 : dist center (h6Config 4) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e12 : dist center (h6Config 1) ^ 2 = dist center (h6Config 2) ^ 2 := by rw [h1, h2]
  have e14 : dist center (h6Config 1) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h1, h4]
  have e15 : dist center (h6Config 1) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h1, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e12 e14 e15
  norm_num at e12 e14 e15
  nlinarith [e12, e14, e15, hs2]

/-- No centre is equidistant from `P1, P3, P4, P5`. -/
theorem h6_not_equidistant_1345 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h1 : dist center (h6Config 1) = r) (h3 : dist center (h6Config 3) = r) (h4 : dist center (h6Config 4) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e13 : dist center (h6Config 1) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h1, h3]
  have e14 : dist center (h6Config 1) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h1, h4]
  have e15 : dist center (h6Config 1) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h1, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e13 e14 e15
  norm_num at e13 e14 e15
  nlinarith [e13, e14, e15, hs2]

/-- No centre is equidistant from `P2, P3, P4, P5`. -/
theorem h6_not_equidistant_2345 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h2 : dist center (h6Config 2) = r) (h3 : dist center (h6Config 3) = r) (h4 : dist center (h6Config 4) = r) (h5 : dist center (h6Config 5) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e23 : dist center (h6Config 2) ^ 2 = dist center (h6Config 3) ^ 2 := by rw [h2, h3]
  have e24 : dist center (h6Config 2) ^ 2 = dist center (h6Config 4) ^ 2 := by rw [h2, h4]
  have e25 : dist center (h6Config 2) ^ 2 = dist center (h6Config 5) ^ 2 := by rw [h2, h5]
  simp only [h6Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs] at e23 e24 e25
  norm_num at e23 e24 e25
  nlinarith [e23, e24, e25, hs2]

set_option maxHeartbeats 6400000 in
/-- **No four of the six points are concyclic.** Every 4-subset is one of the
fifteen quadruples, and for each no centre is equidistant from its members. -/
theorem noFourConcyclic_h6Config : NoFourConcyclic h6Config := by
  intro a b c d hcard
  rintro ⟨center, r, ha, hb, hc, hd⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact h6_not_equidistant_0123 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_0124 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_0125 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_0134 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_0135 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_0145 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_0234 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_0235 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_0245 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_0345 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_1234 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_1235 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_1245 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_1345 center r (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact h6_not_equidistant_2345 center r (by assumption) (by assumption)
        (by assumption) (by assumption)

/-- **`h6Config` is in general position.** -/
theorem inGeneralPosition_h6Config : InGeneralPosition h6Config :=
  ⟨h6Config_injective, noThreeCollinear_h6Config, noFourConcyclic_h6Config⟩

/-- **`h6Config` realizes at most four distinct distances.** Every positive
pairwise distance lies in the four-element set `{1, √3, 2, √7}`. -/
theorem numDistinctDistances_h6Config_le :
    numDistinctDistances h6Config ≤ 4 := by
  unfold numDistinctDistances
  have hsub :
      ((univ.product univ).image
          (fun p : Fin 6 × Fin 6 =>
            dist (h6Config p.1) (h6Config p.2))).filter (· > 0)
        ⊆ ({1, Real.sqrt 3, 2, Real.sqrt 7} : Finset ℝ) := by
    intro d hd
    rw [mem_filter, mem_image] at hd
    obtain ⟨⟨p, -, hpd⟩, hpos⟩ := hd
    have hne : p.1 ≠ p.2 := by
      intro he
      rw [he, dist_self] at hpd
      rw [← hpd] at hpos
      exact lt_irrefl 0 hpos
    rw [← hpd]
    exact h6Config_dist_mem hne
  calc (((univ.product univ).image
          (fun p : Fin 6 × Fin 6 =>
            dist (h6Config p.1) (h6Config p.2))).filter (· > 0)).card
      ≤ ({1, Real.sqrt 3, 2, Real.sqrt 7} : Finset ℝ).card := card_le_card hsub
    _ ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        have h3 : ({Real.sqrt 3, 2, Real.sqrt 7} : Finset ℝ).card ≤ 3 := by
          refine (Finset.card_insert_le _ _).trans ?_
          refine Nat.succ_le_succ ?_
          exact (Finset.card_insert_le _ _).trans (by simp)
        omega

/-- **`h 6 ≤ 4`, the first nontrivial upper bound for `h 6`.** The four-distance
witness `h6Config` is in general position, so it bounds the minimum:
`h 6 ≤ numDistinctDistances h6Config ≤ 4`.  (The best previous ceiling was the
generic `h 6 ≤ 15`.) -/
theorem h_six_le_four : h 6 ≤ 4 :=
  le_trans (h_le_of_inGeneralPosition inGeneralPosition_h6Config)
    numDistinctDistances_h6Config_le

/-- **`3 ≤ h 6 ≤ 4`.** The triangular-lattice four-distance witness gives the
upper bound; `three_le_h_six` (via `h 5 = 3` and monotonicity) gives the lower
bound.  Pinning `h 6` exactly would require either a six-point general-position
three-distance set (`h 6 = 3`) or a proof that none exists (`h 6 = 4`) — open
here. -/
theorem h_six_bounds : 3 ≤ h 6 ∧ h 6 ≤ 4 :=
  ⟨three_le_h_six, h_six_le_four⟩

end Erdos98WIP01
