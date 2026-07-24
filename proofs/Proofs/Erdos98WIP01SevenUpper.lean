/-
  Erdős Problem #98 — Distinct distances in general position:
  the first nontrivial upper bound for seven points — `h 7 ≤ 6` (0-axiom).

  Companion to `Erdos98WIP01.lean` (exact values `h 2 = h 3 = 1`, `h 4 = 2`,
  `h 5 = 3`), `Erdos98WIP01Thresholds.lean` (`3 ≤ h 7` from the five-point
  lower bound and monotonicity), and `Erdos98WIP01SixUpper.lean`
  (`h 6 ∈ {3, 4}` via the twisted-triangle witness `sixConfig`).

  Before this file the only upper bound available for seven points was the
  generic ceiling `h 7 ≤ 7.choose 2 = 21` (`h_le_choose_two`).  This file
  produces an explicit general-position 7-point configuration with exactly SIX
  distinct distances, pinning `h 7 ∈ {3, 4, 5, 6}` (`h_seven_bounds`,
  `h_seven_cases`).

  **The configuration** (`sevenConfig`): the six-point witness `sixConfig`
  (two concentric equilateral triangles, inner circumradius `1` at
  `0°, 120°, 240°`, outer circumradius `√2` at `90°, 210°, 330°`) together
  with their common centre, the origin:

    P₀ = (1, 0)          P₁ = (−1/2, √3/2)     P₂ = (−1/2, −√3/2)
    P₃ = (0, √2)         P₄ = (−√6/2, −√2/2)   P₅ = (√6/2, −√2/2)
    P₆ = (0, 0)

  Squared distances: the fifteen internal pairs realize `{3, 6, 3 + √6, 3 − √6}`
  (proved once in `Erdos98WIP01SixUpper` and REUSED here — the first six points
  of `sevenConfig` are definitionally the six points of `sixConfig`), and the
  six rays from the centre contribute the two circumradii squared: `1` (inner)
  and `2` (outer).  Six values total — distances
  `{1, √2, √3, √6, √(3+√6), √(3−√6)}`.

  **General position** (`C(7,3) = 35` triples, `C(7,4) = 35` quadruples):
  * no 3 collinear — the 20 internal triples reduce definitionally to
    `noThreeCollinear_sixConfig`; the 15 triples through the origin owe the
    cross-product determinant `xᵢyⱼ − yᵢxⱼ`, whose values all lie in
    `{±√2/2, ±√2, ±√3/2, ±√3}` — nonzero by surd positivity.
  * no 4 concyclic — the 15 internal quadruples reduce definitionally to
    `noFourConcyclic_sixConfig`; for the 20 quadruples through the origin the
    circle determinant is anchored AT the origin (`p = P₆`), where it
    simplifies to `Nᵢ·C(j,k) − Nⱼ·C(i,k) + Nₖ·C(i,j)` with `N ∈ {1, 2}` the
    squared radii and `C` the cross products above.  The twenty values are
    `±√3, ±(√3 − 3√2/2), ±(3√2/2 + √3), ±(√3 ± 3√2), 3√3/2, 6√3, 3√2 − √3` —
    all nonzero, the tight ones (`|√3 − 3√2/2| ≈ 0.39`) by the rational
    bracketing `1.414 < √2 < 1.415`, `1.732 < √3 < 1.733`.

  The reduction of the 35 internal obligations to the public six-point
  aggregates (with explicit index arguments) is definitional: `sevenConfig`
  restricted to `{0, …, 5}` and `sixConfig` elaborate to identical
  `!₂[·, ·]` literals.

  Within this witness family nothing better is possible: any 7-point set
  containing the centre of a twisted-triangle pair already realizes the two
  radii beyond the four internal distances.  Whether `h 7 < 6` holds needs a
  structurally different configuration; the exact value of `h 7` remains open
  (as does `h 6 = 3` vs `4`).

  ## Summary: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib
import Proofs.Erdos98WIP01SixUpper

open Finset

namespace Erdos98WIP01

/-! ## Shared surd facts

Same catalogue as `Erdos98WIP01SixUpper` (its copies are `private`, hence
re-recorded here): squares, positivity, pairwise products, and rational
bracketing bounds for `√2, √3, √6`. -/

private theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private theorem sqrt_six_sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

private theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
private theorem sqrt_three_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
private theorem sqrt_six_pos : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)

private theorem sqrt_two_mul_sqrt_three : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem sqrt_two_mul_sqrt_six : Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
  linear_combination (- Real.sqrt 2) * sqrt_two_mul_sqrt_three + Real.sqrt 3 * sqrt_two_sq

private theorem sqrt_three_mul_sqrt_six : Real.sqrt 3 * Real.sqrt 6 = 3 * Real.sqrt 2 := by
  linear_combination (- Real.sqrt 3) * sqrt_two_mul_sqrt_three + Real.sqrt 2 * sqrt_three_sq

private theorem sqrt_two_lt : Real.sqrt 2 < 1.415 := by
  nlinarith [sqrt_two_sq, sqrt_two_pos]

private theorem lt_sqrt_two : (1.414 : ℝ) < Real.sqrt 2 := by
  nlinarith [sqrt_two_sq, sqrt_two_pos]

private theorem sqrt_three_lt : Real.sqrt 3 < 1.733 := by
  nlinarith [sqrt_three_sq, sqrt_three_pos]

private theorem lt_sqrt_three : (1.732 : ℝ) < Real.sqrt 3 := by
  nlinarith [sqrt_three_sq, sqrt_three_pos]

private theorem sqrt_six_lt : Real.sqrt 6 < 2.450 := by
  nlinarith [sqrt_six_sq, sqrt_six_pos]

private theorem lt_sqrt_six : (2.449 : ℝ) < Real.sqrt 6 := by
  nlinarith [sqrt_six_sq, sqrt_six_pos]

/-! ## The configuration -/

/-- **The 6-distance witness**: the six points of `sixConfig` (twisted
concentric equilateral triangles, circumradii `1` and `√2`) together with
their common centre, the origin. -/
noncomputable def sevenConfig : PointConfig 7 :=
  ![!₂[1, 0], !₂[-(1 / 2), Real.sqrt 3 / 2], !₂[-(1 / 2), -(Real.sqrt 3 / 2)],
    !₂[0, Real.sqrt 2], !₂[-(Real.sqrt 6 / 2), -(Real.sqrt 2 / 2)],
    !₂[Real.sqrt 6 / 2, -(Real.sqrt 2 / 2)], !₂[0, 0]]

private theorem sevenConfig_zero : sevenConfig 0 = !₂[1, 0] := rfl
private theorem sevenConfig_one : sevenConfig 1 = !₂[-(1 / 2), Real.sqrt 3 / 2] := rfl
private theorem sevenConfig_two : sevenConfig 2 = !₂[-(1 / 2), -(Real.sqrt 3 / 2)] := rfl
private theorem sevenConfig_three : sevenConfig 3 = !₂[0, Real.sqrt 2] := rfl
private theorem sevenConfig_four : sevenConfig 4 = !₂[-(Real.sqrt 6 / 2), -(Real.sqrt 2 / 2)] := rfl
private theorem sevenConfig_five : sevenConfig 5 = !₂[Real.sqrt 6 / 2, -(Real.sqrt 2 / 2)] := rfl
private theorem sevenConfig_six : sevenConfig 6 = !₂[0, 0] := rfl

/-! ## The twenty-one pairwise squared distances

The fifteen internal pairs REUSE `sixConfig_dist_sq` (the first six points of
`sevenConfig` are definitionally those of `sixConfig`), injected into the wider
six-way disjunction.  The six rays from the centre are the circumradii squared:
`1` for the inner triangle, `2` for the outer. -/

section PairDistances

private theorem seven_dist_01 :
    dist (sevenConfig 0) (sevenConfig 1) ^ 2 = 3 ∨
    dist (sevenConfig 0) (sevenConfig 1) ^ 2 = 6 ∨
    dist (sevenConfig 0) (sevenConfig 1) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 1) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 1) ^ 2 = 1 ∨
    dist (sevenConfig 0) (sevenConfig 1) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 0) (j := 1) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_02 :
    dist (sevenConfig 0) (sevenConfig 2) ^ 2 = 3 ∨
    dist (sevenConfig 0) (sevenConfig 2) ^ 2 = 6 ∨
    dist (sevenConfig 0) (sevenConfig 2) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 2) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 2) ^ 2 = 1 ∨
    dist (sevenConfig 0) (sevenConfig 2) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 0) (j := 2) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_03 :
    dist (sevenConfig 0) (sevenConfig 3) ^ 2 = 3 ∨
    dist (sevenConfig 0) (sevenConfig 3) ^ 2 = 6 ∨
    dist (sevenConfig 0) (sevenConfig 3) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 3) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 3) ^ 2 = 1 ∨
    dist (sevenConfig 0) (sevenConfig 3) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 0) (j := 3) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_04 :
    dist (sevenConfig 0) (sevenConfig 4) ^ 2 = 3 ∨
    dist (sevenConfig 0) (sevenConfig 4) ^ 2 = 6 ∨
    dist (sevenConfig 0) (sevenConfig 4) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 4) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 4) ^ 2 = 1 ∨
    dist (sevenConfig 0) (sevenConfig 4) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 0) (j := 4) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_05 :
    dist (sevenConfig 0) (sevenConfig 5) ^ 2 = 3 ∨
    dist (sevenConfig 0) (sevenConfig 5) ^ 2 = 6 ∨
    dist (sevenConfig 0) (sevenConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 5) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 5) ^ 2 = 1 ∨
    dist (sevenConfig 0) (sevenConfig 5) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 0) (j := 5) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_12 :
    dist (sevenConfig 1) (sevenConfig 2) ^ 2 = 3 ∨
    dist (sevenConfig 1) (sevenConfig 2) ^ 2 = 6 ∨
    dist (sevenConfig 1) (sevenConfig 2) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 2) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 2) ^ 2 = 1 ∨
    dist (sevenConfig 1) (sevenConfig 2) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 1) (j := 2) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_13 :
    dist (sevenConfig 1) (sevenConfig 3) ^ 2 = 3 ∨
    dist (sevenConfig 1) (sevenConfig 3) ^ 2 = 6 ∨
    dist (sevenConfig 1) (sevenConfig 3) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 3) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 3) ^ 2 = 1 ∨
    dist (sevenConfig 1) (sevenConfig 3) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 1) (j := 3) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_14 :
    dist (sevenConfig 1) (sevenConfig 4) ^ 2 = 3 ∨
    dist (sevenConfig 1) (sevenConfig 4) ^ 2 = 6 ∨
    dist (sevenConfig 1) (sevenConfig 4) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 4) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 4) ^ 2 = 1 ∨
    dist (sevenConfig 1) (sevenConfig 4) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 1) (j := 4) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_15 :
    dist (sevenConfig 1) (sevenConfig 5) ^ 2 = 3 ∨
    dist (sevenConfig 1) (sevenConfig 5) ^ 2 = 6 ∨
    dist (sevenConfig 1) (sevenConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 5) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 5) ^ 2 = 1 ∨
    dist (sevenConfig 1) (sevenConfig 5) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 1) (j := 5) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_23 :
    dist (sevenConfig 2) (sevenConfig 3) ^ 2 = 3 ∨
    dist (sevenConfig 2) (sevenConfig 3) ^ 2 = 6 ∨
    dist (sevenConfig 2) (sevenConfig 3) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 2) (sevenConfig 3) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 2) (sevenConfig 3) ^ 2 = 1 ∨
    dist (sevenConfig 2) (sevenConfig 3) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 2) (j := 3) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_24 :
    dist (sevenConfig 2) (sevenConfig 4) ^ 2 = 3 ∨
    dist (sevenConfig 2) (sevenConfig 4) ^ 2 = 6 ∨
    dist (sevenConfig 2) (sevenConfig 4) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 2) (sevenConfig 4) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 2) (sevenConfig 4) ^ 2 = 1 ∨
    dist (sevenConfig 2) (sevenConfig 4) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 2) (j := 4) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_25 :
    dist (sevenConfig 2) (sevenConfig 5) ^ 2 = 3 ∨
    dist (sevenConfig 2) (sevenConfig 5) ^ 2 = 6 ∨
    dist (sevenConfig 2) (sevenConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 2) (sevenConfig 5) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 2) (sevenConfig 5) ^ 2 = 1 ∨
    dist (sevenConfig 2) (sevenConfig 5) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 2) (j := 5) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_34 :
    dist (sevenConfig 3) (sevenConfig 4) ^ 2 = 3 ∨
    dist (sevenConfig 3) (sevenConfig 4) ^ 2 = 6 ∨
    dist (sevenConfig 3) (sevenConfig 4) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 3) (sevenConfig 4) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 3) (sevenConfig 4) ^ 2 = 1 ∨
    dist (sevenConfig 3) (sevenConfig 4) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 3) (j := 4) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_35 :
    dist (sevenConfig 3) (sevenConfig 5) ^ 2 = 3 ∨
    dist (sevenConfig 3) (sevenConfig 5) ^ 2 = 6 ∨
    dist (sevenConfig 3) (sevenConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 3) (sevenConfig 5) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 3) (sevenConfig 5) ^ 2 = 1 ∨
    dist (sevenConfig 3) (sevenConfig 5) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 3) (j := 5) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_45 :
    dist (sevenConfig 4) (sevenConfig 5) ^ 2 = 3 ∨
    dist (sevenConfig 4) (sevenConfig 5) ^ 2 = 6 ∨
    dist (sevenConfig 4) (sevenConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 4) (sevenConfig 5) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 4) (sevenConfig 5) ^ 2 = 1 ∨
    dist (sevenConfig 4) (sevenConfig 5) ^ 2 = 2 := by
  rcases sixConfig_dist_sq (i := 4) (j := 5) (by decide) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem seven_dist_06 :
    dist (sevenConfig 0) (sevenConfig 6) ^ 2 = 3 ∨
    dist (sevenConfig 0) (sevenConfig 6) ^ 2 = 6 ∨
    dist (sevenConfig 0) (sevenConfig 6) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 6) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 0) (sevenConfig 6) ^ 2 = 1 ∨
    dist (sevenConfig 0) (sevenConfig 6) ^ 2 = 2 := by
  right; right; right; right; left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sevenConfig_zero, sevenConfig_six, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem seven_dist_16 :
    dist (sevenConfig 1) (sevenConfig 6) ^ 2 = 3 ∨
    dist (sevenConfig 1) (sevenConfig 6) ^ 2 = 6 ∨
    dist (sevenConfig 1) (sevenConfig 6) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 6) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 1) (sevenConfig 6) ^ 2 = 1 ∨
    dist (sevenConfig 1) (sevenConfig 6) ^ 2 = 2 := by
  right; right; right; right; left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sevenConfig_one, sevenConfig_six, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem seven_dist_26 :
    dist (sevenConfig 2) (sevenConfig 6) ^ 2 = 3 ∨
    dist (sevenConfig 2) (sevenConfig 6) ^ 2 = 6 ∨
    dist (sevenConfig 2) (sevenConfig 6) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 2) (sevenConfig 6) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 2) (sevenConfig 6) ^ 2 = 1 ∨
    dist (sevenConfig 2) (sevenConfig 6) ^ 2 = 2 := by
  right; right; right; right; left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sevenConfig_two, sevenConfig_six, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem seven_dist_36 :
    dist (sevenConfig 3) (sevenConfig 6) ^ 2 = 3 ∨
    dist (sevenConfig 3) (sevenConfig 6) ^ 2 = 6 ∨
    dist (sevenConfig 3) (sevenConfig 6) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 3) (sevenConfig 6) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 3) (sevenConfig 6) ^ 2 = 1 ∨
    dist (sevenConfig 3) (sevenConfig 6) ^ 2 = 2 := by
  right; right; right; right; right
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sevenConfig_three, sevenConfig_six, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem seven_dist_46 :
    dist (sevenConfig 4) (sevenConfig 6) ^ 2 = 3 ∨
    dist (sevenConfig 4) (sevenConfig 6) ^ 2 = 6 ∨
    dist (sevenConfig 4) (sevenConfig 6) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 4) (sevenConfig 6) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 4) (sevenConfig 6) ^ 2 = 1 ∨
    dist (sevenConfig 4) (sevenConfig 6) ^ 2 = 2 := by
  right; right; right; right; right
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sevenConfig_four, sevenConfig_six, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem seven_dist_56 :
    dist (sevenConfig 5) (sevenConfig 6) ^ 2 = 3 ∨
    dist (sevenConfig 5) (sevenConfig 6) ^ 2 = 6 ∨
    dist (sevenConfig 5) (sevenConfig 6) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig 5) (sevenConfig 6) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig 5) (sevenConfig 6) ^ 2 = 1 ∨
    dist (sevenConfig 5) (sevenConfig 6) ^ 2 = 2 := by
  right; right; right; right; right
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sevenConfig_five, sevenConfig_six, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

end PairDistances

set_option maxHeartbeats 1600000 in
/-- **Every pairwise squared distance of `sevenConfig` is `3`, `6`, `3 + √6`,
`3 − √6`, `1`, or `2`.**  Assembled from the twenty-one per-pair lemmas; the
transposed pairs reduce to them by `dist_comm`. -/
theorem sevenConfig_dist_sq {i j : Fin 7} (hij : i ≠ j) :
    dist (sevenConfig i) (sevenConfig j) ^ 2 = 3 ∨
    dist (sevenConfig i) (sevenConfig j) ^ 2 = 6 ∨
    dist (sevenConfig i) (sevenConfig j) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sevenConfig i) (sevenConfig j) ^ 2 = 3 - Real.sqrt 6 ∨
    dist (sevenConfig i) (sevenConfig j) ^ 2 = 1 ∨
    dist (sevenConfig i) (sevenConfig j) ^ 2 = 2 := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact seven_dist_01
    | exact seven_dist_02
    | exact seven_dist_03
    | exact seven_dist_04
    | exact seven_dist_05
    | exact seven_dist_06
    | exact seven_dist_12
    | exact seven_dist_13
    | exact seven_dist_14
    | exact seven_dist_15
    | exact seven_dist_16
    | exact seven_dist_23
    | exact seven_dist_24
    | exact seven_dist_25
    | exact seven_dist_26
    | exact seven_dist_34
    | exact seven_dist_35
    | exact seven_dist_36
    | exact seven_dist_45
    | exact seven_dist_46
    | exact seven_dist_56
    | (rw [dist_comm]
       first
       | exact seven_dist_01
       | exact seven_dist_02
       | exact seven_dist_03
       | exact seven_dist_04
       | exact seven_dist_05
       | exact seven_dist_06
       | exact seven_dist_12
       | exact seven_dist_13
       | exact seven_dist_14
       | exact seven_dist_15
       | exact seven_dist_16
       | exact seven_dist_23
       | exact seven_dist_24
       | exact seven_dist_25
       | exact seven_dist_26
       | exact seven_dist_34
       | exact seven_dist_35
       | exact seven_dist_36
       | exact seven_dist_45
       | exact seven_dist_46
       | exact seven_dist_56)

/-- **Every pairwise distance of `sevenConfig` lies in
`{1, √2, √3, √6, √(3+√6), √(3−√6)}`.**  Nonnegative square roots of
`sevenConfig_dist_sq`. -/
theorem sevenConfig_dist_mem {i j : Fin 7} (hij : i ≠ j) :
    dist (sevenConfig i) (sevenConfig j) ∈
      ({1, Real.sqrt 2, Real.sqrt 3, Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
        Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ) := by
  have hd0 : 0 ≤ dist (sevenConfig i) (sevenConfig j) := dist_nonneg
  rcases sevenConfig_dist_sq hij with h | h | h | h | h | h
  · have he : dist (sevenConfig i) (sevenConfig j) = Real.sqrt 3 := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]
  · have he : dist (sevenConfig i) (sevenConfig j) = Real.sqrt 6 := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]
  · have he : dist (sevenConfig i) (sevenConfig j) = Real.sqrt (3 + Real.sqrt 6) := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]
  · have he : dist (sevenConfig i) (sevenConfig j) = Real.sqrt (3 - Real.sqrt 6) := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]
  · have he : dist (sevenConfig i) (sevenConfig j) = 1 := by
      rw [← Real.sqrt_sq hd0, h, Real.sqrt_one]
    simp [he]
  · have he : dist (sevenConfig i) (sevenConfig j) = Real.sqrt 2 := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]

/-- The seven points are distinct: every pairwise distance lies in a set of six
positive reals, so it never vanishes. -/
theorem sevenConfig_injective : Function.Injective sevenConfig := by
  intro i j hij
  by_contra hne
  have hmem := sevenConfig_dist_mem hne
  rw [hij, dist_self] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hp1 : (0 : ℝ) < Real.sqrt (3 + Real.sqrt 6) :=
    Real.sqrt_pos.mpr (by positivity)
  have hp2 : (0 : ℝ) < Real.sqrt (3 - Real.sqrt 6) :=
    Real.sqrt_pos.mpr (by linarith [sqrt_six_lt])
  rcases hmem with h | h | h | h | h | h
  · linarith [one_pos]
  · linarith [sqrt_two_pos]
  · linarith [sqrt_three_pos]
  · linarith [sqrt_six_pos]
  · linarith [hp1]
  · linarith [hp2]

/-! ## No three collinear: 35 triples

The 20 internal triples reduce definitionally to `noThreeCollinear_sixConfig`
(the public six-point aggregate, applied at explicit indices).  The 15 triples
through the origin each owe the cross-product determinant `xᵢyⱼ − yᵢxⱼ`
(the line criterion `not_collinear_of_det` evaluated at `r = origin`), whose
values lie in `{±√2/2, ±√2, ±√3/2, ±√3}`. -/

section NoLine

private theorem seven_noLine_012 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 1 2 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_013 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 1 3 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_014 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 1 4 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_015 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 1 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_023 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 2 3 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_024 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 2 4 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_025 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 2 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_034 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 3 4 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_035 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 3 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_045 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 0 4 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_123 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 1 2 3 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_124 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 1 2 4 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_125 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 1 2 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_134 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 1 3 4 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_135 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 1 3 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_145 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 1 4 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_234 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 2 3 4 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_235 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 2 3 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_245 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 2 4 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_345 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 :=
  fun ⟨a, b, c, hne, h1, h2, h3⟩ =>
    noThreeCollinear_sixConfig 3 4 5 (by decide) ⟨a, b, c, hne, h1, h2, h3⟩

private theorem seven_noLine_016 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_zero, sevenConfig_one, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_026 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_zero, sevenConfig_two, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_036 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_zero, sevenConfig_three, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_046 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_zero, sevenConfig_four, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_056 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_zero, sevenConfig_five, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_126 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_one, sevenConfig_two, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_136 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_one, sevenConfig_three, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_146 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_one, sevenConfig_four, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_156 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_one, sevenConfig_five, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_236 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_two, sevenConfig_three, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_246 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_two, sevenConfig_four, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_256 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_two, sevenConfig_five, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_346 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_three, sevenConfig_four, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_356 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_three, sevenConfig_five, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noLine_456 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0 ∧
      a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0 ∧
      a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sevenConfig_four, sevenConfig_five, sevenConfig_six]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

end NoLine

/-! ### Dispatch: one helper per first index, then the aggregate -/

set_option maxHeartbeats 800000 in
private theorem sevenConfig_noLine_with_0 (j k : Fin 7)
    (hcard : ({(0 : Fin 7), j, k} : Finset (Fin 7)).card = 3)
    (a b c : ℝ) (hne : (a, b, c) ≠ (0, 0, 0))
    (e1 : a * (sevenConfig 0 0) + b * (sevenConfig 0 1) + c = 0)
    (e2 : a * (sevenConfig j 0) + b * (sevenConfig j 1) + c = 0)
    (e3 : a * (sevenConfig k 0) + b * (sevenConfig k 1) + c = 0) : False := by
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noLine_012 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_013 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_014 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_015 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_016 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_023 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_024 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_025 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_026 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_034 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_035 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_036 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_045 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_046 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_056 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 800000 in
private theorem sevenConfig_noLine_with_1 (j k : Fin 7)
    (hcard : ({(1 : Fin 7), j, k} : Finset (Fin 7)).card = 3)
    (a b c : ℝ) (hne : (a, b, c) ≠ (0, 0, 0))
    (e1 : a * (sevenConfig 1 0) + b * (sevenConfig 1 1) + c = 0)
    (e2 : a * (sevenConfig j 0) + b * (sevenConfig j 1) + c = 0)
    (e3 : a * (sevenConfig k 0) + b * (sevenConfig k 1) + c = 0) : False := by
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noLine_012 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_013 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_014 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_015 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_016 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_123 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_124 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_125 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_126 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_134 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_135 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_136 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_145 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_146 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_156 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 800000 in
private theorem sevenConfig_noLine_with_2 (j k : Fin 7)
    (hcard : ({(2 : Fin 7), j, k} : Finset (Fin 7)).card = 3)
    (a b c : ℝ) (hne : (a, b, c) ≠ (0, 0, 0))
    (e1 : a * (sevenConfig 2 0) + b * (sevenConfig 2 1) + c = 0)
    (e2 : a * (sevenConfig j 0) + b * (sevenConfig j 1) + c = 0)
    (e3 : a * (sevenConfig k 0) + b * (sevenConfig k 1) + c = 0) : False := by
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noLine_012 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_023 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_024 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_025 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_026 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_123 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_124 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_125 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_126 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_234 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_235 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_236 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_245 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_246 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_256 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 800000 in
private theorem sevenConfig_noLine_with_3 (j k : Fin 7)
    (hcard : ({(3 : Fin 7), j, k} : Finset (Fin 7)).card = 3)
    (a b c : ℝ) (hne : (a, b, c) ≠ (0, 0, 0))
    (e1 : a * (sevenConfig 3 0) + b * (sevenConfig 3 1) + c = 0)
    (e2 : a * (sevenConfig j 0) + b * (sevenConfig j 1) + c = 0)
    (e3 : a * (sevenConfig k 0) + b * (sevenConfig k 1) + c = 0) : False := by
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noLine_013 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_023 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_036 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_123 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_034 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_035 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_134 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_135 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_136 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_234 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_235 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_236 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_345 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_346 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_356 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 800000 in
private theorem sevenConfig_noLine_with_4 (j k : Fin 7)
    (hcard : ({(4 : Fin 7), j, k} : Finset (Fin 7)).card = 3)
    (a b c : ℝ) (hne : (a, b, c) ≠ (0, 0, 0))
    (e1 : a * (sevenConfig 4 0) + b * (sevenConfig 4 1) + c = 0)
    (e2 : a * (sevenConfig j 0) + b * (sevenConfig j 1) + c = 0)
    (e3 : a * (sevenConfig k 0) + b * (sevenConfig k 1) + c = 0) : False := by
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noLine_014 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_024 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_046 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_124 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_034 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_045 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_134 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_145 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_146 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_234 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_245 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_246 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_345 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_346 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_456 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 800000 in
private theorem sevenConfig_noLine_with_5 (j k : Fin 7)
    (hcard : ({(5 : Fin 7), j, k} : Finset (Fin 7)).card = 3)
    (a b c : ℝ) (hne : (a, b, c) ≠ (0, 0, 0))
    (e1 : a * (sevenConfig 5 0) + b * (sevenConfig 5 1) + c = 0)
    (e2 : a * (sevenConfig j 0) + b * (sevenConfig j 1) + c = 0)
    (e3 : a * (sevenConfig k 0) + b * (sevenConfig k 1) + c = 0) : False := by
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noLine_015 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_025 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_056 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_125 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_035 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_045 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_135 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_145 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_156 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_235 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_245 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_256 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_345 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_356 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_456 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 800000 in
private theorem sevenConfig_noLine_with_6 (j k : Fin 7)
    (hcard : ({(6 : Fin 7), j, k} : Finset (Fin 7)).card = 3)
    (a b c : ℝ) (hne : (a, b, c) ≠ (0, 0, 0))
    (e1 : a * (sevenConfig 6 0) + b * (sevenConfig 6 1) + c = 0)
    (e2 : a * (sevenConfig j 0) + b * (sevenConfig j 1) + c = 0)
    (e3 : a * (sevenConfig k 0) + b * (sevenConfig k 1) + c = 0) : False := by
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noLine_016 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_026 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_036 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_046 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_056 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_126 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_136 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_146 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_156 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_236 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_246 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_256 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_346 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_356 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact seven_noLine_456 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩

/-- **No three of the seven points are collinear.**  The first index is split
into seven helper lemmas (one per value); every genuine index triple then
dispatches (via `assumption`, so in any order) to one of the thirty-five
per-triple line-determinant lemmas. -/
theorem noThreeCollinear_sevenConfig : NoThreeCollinear sevenConfig := by
  intro i j k hcard
  rintro ⟨a, b, c, hne, e1, e2, e3⟩
  fin_cases i
  · exact sevenConfig_noLine_with_0 j k hcard a b c hne e1 e2 e3
  · exact sevenConfig_noLine_with_1 j k hcard a b c hne e1 e2 e3
  · exact sevenConfig_noLine_with_2 j k hcard a b c hne e1 e2 e3
  · exact sevenConfig_noLine_with_3 j k hcard a b c hne e1 e2 e3
  · exact sevenConfig_noLine_with_4 j k hcard a b c hne e1 e2 e3
  · exact sevenConfig_noLine_with_5 j k hcard a b c hne e1 e2 e3
  · exact sevenConfig_noLine_with_6 j k hcard a b c hne e1 e2 e3

/-! ## No four concyclic: 35 quadruples

The 15 internal quadruples reduce definitionally to
`noFourConcyclic_sixConfig`.  For the 20 quadruples through the origin the
circle determinant of `not_concyclic_of_det` is anchored AT the origin
(`p = P₆`, so `N_p = 0`), where it evaluates to
`Nᵢ·C(j,k) − Nⱼ·C(i,k) + Nₖ·C(i,j)` with `N ∈ {1, 2}` the squared radii and
`C(i,j) = xᵢyⱼ − yᵢxⱼ` the cross products of the collinearity block. -/

section NoCircle

private theorem seven_noCircle_0123 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 3) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 1 2 3 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_0124 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 4) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 1 2 4 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_0125 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 1 2 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_0134 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 4) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 1 3 4 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_0135 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 1 3 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_0145 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 1 4 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_0234 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 2) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 4) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 2 3 4 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_0235 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 2) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 2 3 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_0245 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 2) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 2 4 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_0345 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 0) = ρ ∧ dist center (sevenConfig 3) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 0 3 4 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_1234 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 1) = ρ ∧ dist center (sevenConfig 2) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 4) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 1 2 3 4 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_1235 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 1) = ρ ∧ dist center (sevenConfig 2) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 1 2 3 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_1245 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 1) = ρ ∧ dist center (sevenConfig 2) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 1 2 4 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_1345 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 1) = ρ ∧ dist center (sevenConfig 3) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 1 3 4 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

private theorem seven_noCircle_2345 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 3) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ :=
  fun ⟨center, ρ, h1, h2, h3, h4⟩ =>
    noFourConcyclic_sixConfig 2 3 4 5 (by decide) ⟨center, ρ, h1, h2, h3, h4⟩

/- The 20 origin quadruples.  Each statement anchors the criterion at the
origin (`P₆` first), where the determinant takes the simple radius/cross form
recorded in the header. -/

private theorem seven_noCircle_0126 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 1) = ρ ∧ dist center (sevenConfig 2) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_one, sevenConfig_two]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_0136 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 1) = ρ ∧ dist center (sevenConfig 3) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_one, sevenConfig_three]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_0146 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 1) = ρ ∧ dist center (sevenConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_one, sevenConfig_four]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_0156 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 1) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_one, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_0236 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 3) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_two, sevenConfig_three]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_0246 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_two, sevenConfig_four]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_0256 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_two, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_0346 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_three, sevenConfig_four]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_0356 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_three, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_0456 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 0) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_zero, sevenConfig_four, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_1236 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 3) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_one, sevenConfig_two, sevenConfig_three]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_1246 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_one, sevenConfig_two, sevenConfig_four]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_1256 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 2) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_one, sevenConfig_two, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_1346 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_one, sevenConfig_three, sevenConfig_four]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_1356 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_one, sevenConfig_three, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_1456 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 1) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_one, sevenConfig_four, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_2346 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 2) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_two, sevenConfig_three, sevenConfig_four]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_2356 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 2) = ρ ∧
      dist center (sevenConfig 3) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_two, sevenConfig_three, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_2456 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 2) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_two, sevenConfig_four, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

private theorem seven_noCircle_3456 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sevenConfig 6) = ρ ∧ dist center (sevenConfig 3) = ρ ∧
      dist center (sevenConfig 4) = ρ ∧ dist center (sevenConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sevenConfig_six, sevenConfig_three, sevenConfig_four, sevenConfig_five]
  norm_num
  all_goals first
    | (intro heq
       nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
         sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
         sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
         sqrt_six_lt, lt_sqrt_six])
    | (constructor <;>
        (intro heq
         nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
           sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
           sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
           sqrt_six_lt, lt_sqrt_six]))

end NoCircle

/-! ### Dispatch: one helper per first index, then the aggregate -/

set_option maxHeartbeats 6400000 in
private theorem sevenConfig_noCircle_with_0 (b c d : Fin 7)
    (hcard : ({(0 : Fin 7), b, c, d} : Finset (Fin 7)).card = 4)
    (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (h1 : dist center (sevenConfig 0) = ρ) (h2 : dist center (sevenConfig b) = ρ)
    (h3 : dist center (sevenConfig c) = ρ) (h4 : dist center (sevenConfig d) = ρ) : False := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noCircle_0123
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0124
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0125
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0126
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0134
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0135
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0136
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0145
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0146
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0156
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0236
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0246
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0256
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 6400000 in
private theorem sevenConfig_noCircle_with_1 (b c d : Fin 7)
    (hcard : ({(1 : Fin 7), b, c, d} : Finset (Fin 7)).card = 4)
    (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (h1 : dist center (sevenConfig 1) = ρ) (h2 : dist center (sevenConfig b) = ρ)
    (h3 : dist center (sevenConfig c) = ρ) (h4 : dist center (sevenConfig d) = ρ) : False := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noCircle_0123
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0124
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0125
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0126
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0134
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0135
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0136
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0145
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0146
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0156
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1236
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1246
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1256
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 6400000 in
private theorem sevenConfig_noCircle_with_2 (b c d : Fin 7)
    (hcard : ({(2 : Fin 7), b, c, d} : Finset (Fin 7)).card = 4)
    (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (h1 : dist center (sevenConfig 2) = ρ) (h2 : dist center (sevenConfig b) = ρ)
    (h3 : dist center (sevenConfig c) = ρ) (h4 : dist center (sevenConfig d) = ρ) : False := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noCircle_0123
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0124
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0125
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0126
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0236
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0246
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0256
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1236
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1246
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1256
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 6400000 in
private theorem sevenConfig_noCircle_with_3 (b c d : Fin 7)
    (hcard : ({(3 : Fin 7), b, c, d} : Finset (Fin 7)).card = 4)
    (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (h1 : dist center (sevenConfig 3) = ρ) (h2 : dist center (sevenConfig b) = ρ)
    (h3 : dist center (sevenConfig c) = ρ) (h4 : dist center (sevenConfig d) = ρ) : False := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noCircle_0123
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0134
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0135
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0136
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0236
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1236
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_3456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 6400000 in
private theorem sevenConfig_noCircle_with_4 (b c d : Fin 7)
    (hcard : ({(4 : Fin 7), b, c, d} : Finset (Fin 7)).card = 4)
    (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (h1 : dist center (sevenConfig 4) = ρ) (h2 : dist center (sevenConfig b) = ρ)
    (h3 : dist center (sevenConfig c) = ρ) (h4 : dist center (sevenConfig d) = ρ) : False := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noCircle_0124
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0134
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0145
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0146
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0246
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1246
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_3456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 6400000 in
private theorem sevenConfig_noCircle_with_5 (b c d : Fin 7)
    (hcard : ({(5 : Fin 7), b, c, d} : Finset (Fin 7)).card = 4)
    (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (h1 : dist center (sevenConfig 5) = ρ) (h2 : dist center (sevenConfig b) = ρ)
    (h3 : dist center (sevenConfig c) = ρ) (h4 : dist center (sevenConfig d) = ρ) : False := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noCircle_0125
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0135
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0145
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0156
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0256
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1256
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_3456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩

set_option maxHeartbeats 6400000 in
private theorem sevenConfig_noCircle_with_6 (b c d : Fin 7)
    (hcard : ({(6 : Fin 7), b, c, d} : Finset (Fin 7)).card = 4)
    (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (h1 : dist center (sevenConfig 6) = ρ) (h2 : dist center (sevenConfig b) = ρ)
    (h3 : dist center (sevenConfig c) = ρ) (h4 : dist center (sevenConfig d) = ρ) : False := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact seven_noCircle_0126
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0136
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0146
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0156
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0236
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0246
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0256
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_0456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1236
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1246
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1256
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_1456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2346
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2356
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_2456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact seven_noCircle_3456
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩

/-- **No four of the seven points are concyclic.**  The first index is split
into seven helper lemmas (one per value, keeping each within its own heartbeat
budget); every genuine index quadruple then dispatches (via `assumption`, so in
any order) to one of the thirty-five per-quadruple circle-determinant lemmas. -/
theorem noFourConcyclic_sevenConfig : NoFourConcyclic sevenConfig := by
  intro a b c d hcard
  rintro ⟨center, ρ, h1, h2, h3, h4⟩
  fin_cases a
  · exact sevenConfig_noCircle_with_0 b c d hcard center ρ h1 h2 h3 h4
  · exact sevenConfig_noCircle_with_1 b c d hcard center ρ h1 h2 h3 h4
  · exact sevenConfig_noCircle_with_2 b c d hcard center ρ h1 h2 h3 h4
  · exact sevenConfig_noCircle_with_3 b c d hcard center ρ h1 h2 h3 h4
  · exact sevenConfig_noCircle_with_4 b c d hcard center ρ h1 h2 h3 h4
  · exact sevenConfig_noCircle_with_5 b c d hcard center ρ h1 h2 h3 h4
  · exact sevenConfig_noCircle_with_6 b c d hcard center ρ h1 h2 h3 h4

/-- **`sevenConfig` is in general position.** -/
theorem inGeneralPosition_sevenConfig : InGeneralPosition sevenConfig :=
  ⟨sevenConfig_injective, noThreeCollinear_sevenConfig, noFourConcyclic_sevenConfig⟩

/-- **`sevenConfig` realizes at most six distinct distances.**  Every positive
pairwise distance lies in the six-element set
`{1, √2, √3, √6, √(3+√6), √(3−√6)}` (`sevenConfig_dist_mem`), so the
distinct-distance count is at most `6`. -/
theorem numDistinctDistances_sevenConfig_le :
    numDistinctDistances sevenConfig ≤ 6 := by
  unfold numDistinctDistances
  have hsub :
      ((univ.product univ).image
          (fun p : Fin 7 × Fin 7 =>
            dist (sevenConfig p.1) (sevenConfig p.2))).filter (· > 0)
        ⊆ ({1, Real.sqrt 2, Real.sqrt 3, Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
            Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ) := by
    intro d hd
    rw [mem_filter, mem_image] at hd
    obtain ⟨⟨p, -, hpd⟩, hpos⟩ := hd
    have hne : p.1 ≠ p.2 := by
      intro he
      rw [he, dist_self] at hpd
      rw [← hpd] at hpos
      exact lt_irrefl 0 hpos
    rw [← hpd]
    exact sevenConfig_dist_mem hne
  calc (((univ.product univ).image
          (fun p : Fin 7 × Fin 7 =>
            dist (sevenConfig p.1) (sevenConfig p.2))).filter (· > 0)).card
      ≤ ({1, Real.sqrt 2, Real.sqrt 3, Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
          Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card := card_le_card hsub
    _ ≤ ({Real.sqrt 2, Real.sqrt 3, Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
          Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card + 1 := card_insert_le _ _
    _ ≤ (({Real.sqrt 3, Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
          Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card + 1) + 1 :=
        Nat.add_le_add_right (card_insert_le _ _) 1
    _ ≤ ((({Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
          Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card + 1) + 1) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_right (card_insert_le _ _) 1) 1
    _ ≤ (((({Real.sqrt (3 + Real.sqrt 6),
          Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card + 1) + 1) + 1) + 1 :=
        Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.add_le_add_right (card_insert_le _ _) 1) 1) 1
    _ ≤ ((((({Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card + 1) + 1) + 1) + 1) + 1 :=
        Nat.add_le_add_right
          (Nat.add_le_add_right
            (Nat.add_le_add_right (Nat.add_le_add_right (card_insert_le _ _) 1) 1) 1) 1
    _ = 6 := by simp

/-! ## The bounds -/

/-- **`h 7 ≤ 6`.**  The explicit general-position six-distance witness
`sevenConfig` caps the minimum.  Before this theorem the best upper bound was
the generic `h 7 ≤ 21` from `h_le_choose_two`. -/
theorem h_seven_le_six : h 7 ≤ 6 :=
  le_trans (h_le_of_inGeneralPosition inGeneralPosition_sevenConfig)
    numDistinctDistances_sevenConfig_le

/-- **`3 ≤ h 7 ≤ 6`.**  Lower bound from `h 5 = 3` and monotonicity
(`three_le_h_seven`, in `Erdos98WIP01Thresholds`); upper bound from
`sevenConfig`. -/
theorem h_seven_bounds : 3 ≤ h 7 ∧ h 7 ≤ 6 :=
  ⟨three_le_h_seven, h_seven_le_six⟩

/-- **The seven-point window: `h 7 ∈ {3, 4, 5, 6}`.**  Pinning the exact value
is open — as is already the six-point dichotomy `h 6 = 3` vs `4`. -/
theorem h_seven_cases : h 7 = 3 ∨ h 7 = 4 ∨ h 7 = 5 ∨ h 7 = 6 := by
  have h1 := three_le_h_seven
  have h2 := h_seven_le_six
  omega

end Erdos98WIP01
