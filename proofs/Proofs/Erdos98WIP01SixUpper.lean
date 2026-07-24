/-
  Erdős Problem #98 — Distinct distances in general position:
  the first nontrivial upper bound for six points — `h 6 ≤ 4` (0-axiom).

  Companion to `Erdos98WIP01.lean` (exact values `h 2 = h 3 = 1`, `h 4 = 2`,
  `h 5 = 3`) and `Erdos98WIP01Thresholds.lean` (`3 ≤ h 6` from monotonicity).

  Before this file the only upper bound available for six points was the generic
  ceiling `h 6 ≤ 6.choose 2 = 15` (`h_le_choose_two`).  The blocked-route registry
  records that pinning the exact value `h 6 = 3` needs a general-position 6-point
  3-distance configuration whose existence is itself open.  This file does what IS
  reachable: an explicit general-position 6-point configuration with exactly FOUR
  distinct distances, pinning `h 6 ∈ {3, 4}` (`h_six_bounds`,
  `h_six_eq_three_or_four`).

  **The configuration** (`sixConfig`): two concentric equilateral triangles,
  inner of circumradius `1` at angles `0°, 120°, 240°`, outer of circumradius `√2`
  at angles `90°, 210°, 330°` (twist `90°`):

    P₀ = (1, 0)          P₁ = (−1/2, √3/2)     P₂ = (−1/2, −√3/2)
    P₃ = (0, √2)         P₄ = (−√6/2, −√2/2)   P₅ = (√6/2, −√2/2)

  Squared distances: inner side `3`, outer side `6`, and cross distances
  `|B − A|² = 3 − 2√2·cos Δ` for twist angles `Δ ∈ {90°, 210°, 330°}`, i.e.
  `3`, `3 + √6`, `3 − √6`.  The `Δ = 90°` cross orbit MERGES with the inner side
  (that is the point of the `√2` radius: `R² = 2r²` makes the `cos Δ = 0` cross
  distance equal the inner side), so only four values `{3, 6, 3 + √6, 3 − √6}`
  occur — distances `{√3, √6, √(3+√6), √(3−√6)}`.

  **General position**:
  * no 3 collinear — all 20 triple determinants are nonzero;
  * no 4 concyclic — the two circumcircles are concentric of different radii, so
    a 3+1 split fails on radii; a 2+2 split would need an inner chord parallel to
    an outer chord, but inner chord directions are `{30°, 90°, 150°}` and outer
    ones `{0°, 60°, 120°}` — disjoint.  Formally, all 15 concyclicity
    determinants are nonzero.

  Both conditions are verified through two new GENERAL determinant criteria
  (`not_collinear_of_det`, `not_concyclic_of_det`) whose proofs are deterministic
  `linear_combination` cofactor identities — no per-case search with unknown
  line/centre coordinates, unlike the `h5Config` treatment.  Each of the 35
  concrete obligations is then a numeric surd inequality.

  Within the twisted-triangle two-parameter family `(R, θ)` a THREE-distance
  merge is impossible in general position: forcing a third coincidence drives
  `(R, θ)` to `(2, ±60°)`, whose configuration is degenerate (it contains the
  collinear triple `(−√3, 1), (0, 1), (√3, 1)`), or to `R = 1` (the triangles
  coincide).  So `h 6 = 3`, if true, needs a construction outside this family —
  consistent with the blocked-route registry entry for exact `h 6`.

  ## Summary: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib
import Proofs.Erdos98WIP01Thresholds

open Finset

namespace Erdos98WIP01

/-! ## Shared surd facts

All arithmetic below lives in `ℚ(√2, √3)` (with `√6 = √2·√3`).  We record the
squares, positivity, pairwise products, and rational bracketing bounds once. -/

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

/-! ## General determinant criteria for the two nondegeneracy conditions

Unlike the `h5Config` treatment (which ran `nlinarith` searches over unknown
line coefficients / circle centres in every case), we prove two reusable
criteria once, by deterministic cofactor `linear_combination` identities.  Each
concrete triple/quadruple then only owes a NUMERIC determinant `≠ 0`. -/

/-- **Line-determinant criterion.**  If the affine determinant
`(q₀−p₀)(r₁−p₁) − (r₀−p₀)(q₁−p₁)` is nonzero (twice the signed triangle area),
no line `a·x + b·y + c = 0` with `(a,b,c) ≠ 0` passes through `p, q, r`.
Eliminating `a`, then `b`, is a cofactor `linear_combination` of the two chord
differences of the line equations. -/
theorem not_collinear_of_det {p q r : EuclideanSpace ℝ (Fin 2)}
    (hdet : (q 0 - p 0) * (r 1 - p 1) - (r 0 - p 0) * (q 1 - p 1) ≠ 0) :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (p 0) + b * (p 1) + c = 0 ∧
      a * (q 0) + b * (q 1) + c = 0 ∧
      a * (r 0) + b * (r 1) + c = 0 := by
  rintro ⟨a, b, c, hne, hp, hq, hr⟩
  have h1 : a * (q 0 - p 0) + b * (q 1 - p 1) = 0 := by linear_combination hq - hp
  have h2 : a * (r 0 - p 0) + b * (r 1 - p 1) = 0 := by linear_combination hr - hp
  have ha : a = 0 := by
    have h3 : a * ((q 0 - p 0) * (r 1 - p 1) - (r 0 - p 0) * (q 1 - p 1)) = 0 := by
      linear_combination (r 1 - p 1) * h1 - (q 1 - p 1) * h2
    exact (mul_eq_zero.mp h3).resolve_right hdet
  have hb : b = 0 := by
    have h3 : b * ((q 0 - p 0) * (r 1 - p 1) - (r 0 - p 0) * (q 1 - p 1)) = 0 := by
      linear_combination (-(r 0 - p 0)) * h1 + (q 0 - p 0) * h2
    exact (mul_eq_zero.mp h3).resolve_right hdet
  have hc : c = 0 := by linear_combination hp - (p 0) * ha - (p 1) * hb
  exact hne (by rw [ha, hb, hc])

/-- **Circle-determinant criterion.**  Writing `N t = t₀² + t₁²`, if the 3×3
determinant `det [[q−p, Nq−Np], [r−p, Nr−Np], [s−p, Ns−Np]]` (expanded along its
last column below) is nonzero, then no centre is equidistant from `p, q, r, s` —
the four points are not concyclic.  Equidistance gives three chord equations
`2c·(t−p) = Nt−Np` linear in the centre `c`; the cofactor combination of the
three equations eliminates `c` identically and evaluates the determinant, which
must then vanish. -/
theorem not_concyclic_of_det {p q r s : EuclideanSpace ℝ (Fin 2)}
    (hdet :
      ((q 0) ^ 2 + (q 1) ^ 2 - (p 0) ^ 2 - (p 1) ^ 2) *
          ((r 0 - p 0) * (s 1 - p 1) - (s 0 - p 0) * (r 1 - p 1))
        - ((r 0) ^ 2 + (r 1) ^ 2 - (p 0) ^ 2 - (p 1) ^ 2) *
          ((q 0 - p 0) * (s 1 - p 1) - (s 0 - p 0) * (q 1 - p 1))
        + ((s 0) ^ 2 + (s 1) ^ 2 - (p 0) ^ 2 - (p 1) ^ 2) *
          ((q 0 - p 0) * (r 1 - p 1) - (r 0 - p 0) * (q 1 - p 1)) ≠ 0) :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center p = ρ ∧ dist center q = ρ ∧ dist center r = ρ ∧ dist center s = ρ := by
  rintro ⟨c, ρ, hp, hq, hr, hs⟩
  apply hdet
  have eq1 : dist c q ^ 2 = dist c p ^ 2 := by rw [hq, hp]
  have eq2 : dist c r ^ 2 = dist c p ^ 2 := by rw [hr, hp]
  have eq3 : dist c s ^ 2 = dist c p ^ 2 := by rw [hs, hp]
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs] at eq1 eq2 eq3
  linear_combination
    ((r 0 - p 0) * (s 1 - p 1) - (s 0 - p 0) * (r 1 - p 1)) * eq1
      - ((q 0 - p 0) * (s 1 - p 1) - (s 0 - p 0) * (q 1 - p 1)) * eq2
      + ((q 0 - p 0) * (r 1 - p 1) - (r 0 - p 0) * (q 1 - p 1)) * eq3

/-! ## The configuration -/

/-- **The 4-distance witness**: inner equilateral triangle of circumradius `1`
(angles `0°, 120°, 240°`) and outer equilateral triangle of circumradius `√2`
(angles `90°, 210°, 330°`). -/
noncomputable def sixConfig : PointConfig 6 :=
  ![!₂[1, 0], !₂[-(1 / 2), Real.sqrt 3 / 2], !₂[-(1 / 2), -(Real.sqrt 3 / 2)],
    !₂[0, Real.sqrt 2], !₂[-(Real.sqrt 6 / 2), -(Real.sqrt 2 / 2)],
    !₂[Real.sqrt 6 / 2, -(Real.sqrt 2 / 2)]]

private theorem sixConfig_zero : sixConfig 0 = !₂[1, 0] := rfl
private theorem sixConfig_one : sixConfig 1 = !₂[-(1 / 2), Real.sqrt 3 / 2] := rfl
private theorem sixConfig_two : sixConfig 2 = !₂[-(1 / 2), -(Real.sqrt 3 / 2)] := rfl
private theorem sixConfig_three : sixConfig 3 = !₂[0, Real.sqrt 2] := rfl
private theorem sixConfig_four : sixConfig 4 = !₂[-(Real.sqrt 6 / 2), -(Real.sqrt 2 / 2)] := rfl
private theorem sixConfig_five : sixConfig 5 = !₂[Real.sqrt 6 / 2, -(Real.sqrt 2 / 2)] := rfl

/-! ## The fifteen pairwise squared distances

One deterministic lemma per unordered pair (no branch search): the value is
injected into the four-way disjunction up front, and the coordinate computation
is closed by `norm_num` plus the recorded surd facts. -/

section PairDistances

private theorem six_dist_01 :
    dist (sixConfig 0) (sixConfig 1) ^ 2 = 3 ∨
    dist (sixConfig 0) (sixConfig 1) ^ 2 = 6 ∨
    dist (sixConfig 0) (sixConfig 1) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 0) (sixConfig 1) ^ 2 = 3 - Real.sqrt 6 := by
  left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_zero, sixConfig_one, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_02 :
    dist (sixConfig 0) (sixConfig 2) ^ 2 = 3 ∨
    dist (sixConfig 0) (sixConfig 2) ^ 2 = 6 ∨
    dist (sixConfig 0) (sixConfig 2) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 0) (sixConfig 2) ^ 2 = 3 - Real.sqrt 6 := by
  left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_zero, sixConfig_two, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_03 :
    dist (sixConfig 0) (sixConfig 3) ^ 2 = 3 ∨
    dist (sixConfig 0) (sixConfig 3) ^ 2 = 6 ∨
    dist (sixConfig 0) (sixConfig 3) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 0) (sixConfig 3) ^ 2 = 3 - Real.sqrt 6 := by
  left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_zero, sixConfig_three, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_04 :
    dist (sixConfig 0) (sixConfig 4) ^ 2 = 3 ∨
    dist (sixConfig 0) (sixConfig 4) ^ 2 = 6 ∨
    dist (sixConfig 0) (sixConfig 4) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 0) (sixConfig 4) ^ 2 = 3 - Real.sqrt 6 := by
  right; right; left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_zero, sixConfig_four, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_05 :
    dist (sixConfig 0) (sixConfig 5) ^ 2 = 3 ∨
    dist (sixConfig 0) (sixConfig 5) ^ 2 = 6 ∨
    dist (sixConfig 0) (sixConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 0) (sixConfig 5) ^ 2 = 3 - Real.sqrt 6 := by
  right; right; right
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_zero, sixConfig_five, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_12 :
    dist (sixConfig 1) (sixConfig 2) ^ 2 = 3 ∨
    dist (sixConfig 1) (sixConfig 2) ^ 2 = 6 ∨
    dist (sixConfig 1) (sixConfig 2) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 1) (sixConfig 2) ^ 2 = 3 - Real.sqrt 6 := by
  left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_one, sixConfig_two, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_13 :
    dist (sixConfig 1) (sixConfig 3) ^ 2 = 3 ∨
    dist (sixConfig 1) (sixConfig 3) ^ 2 = 6 ∨
    dist (sixConfig 1) (sixConfig 3) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 1) (sixConfig 3) ^ 2 = 3 - Real.sqrt 6 := by
  right; right; right
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_one, sixConfig_three, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_14 :
    dist (sixConfig 1) (sixConfig 4) ^ 2 = 3 ∨
    dist (sixConfig 1) (sixConfig 4) ^ 2 = 6 ∨
    dist (sixConfig 1) (sixConfig 4) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 1) (sixConfig 4) ^ 2 = 3 - Real.sqrt 6 := by
  left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_one, sixConfig_four, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_15 :
    dist (sixConfig 1) (sixConfig 5) ^ 2 = 3 ∨
    dist (sixConfig 1) (sixConfig 5) ^ 2 = 6 ∨
    dist (sixConfig 1) (sixConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 1) (sixConfig 5) ^ 2 = 3 - Real.sqrt 6 := by
  right; right; left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_one, sixConfig_five, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_23 :
    dist (sixConfig 2) (sixConfig 3) ^ 2 = 3 ∨
    dist (sixConfig 2) (sixConfig 3) ^ 2 = 6 ∨
    dist (sixConfig 2) (sixConfig 3) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 2) (sixConfig 3) ^ 2 = 3 - Real.sqrt 6 := by
  right; right; left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_two, sixConfig_three, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_24 :
    dist (sixConfig 2) (sixConfig 4) ^ 2 = 3 ∨
    dist (sixConfig 2) (sixConfig 4) ^ 2 = 6 ∨
    dist (sixConfig 2) (sixConfig 4) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 2) (sixConfig 4) ^ 2 = 3 - Real.sqrt 6 := by
  right; right; right
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_two, sixConfig_four, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_25 :
    dist (sixConfig 2) (sixConfig 5) ^ 2 = 3 ∨
    dist (sixConfig 2) (sixConfig 5) ^ 2 = 6 ∨
    dist (sixConfig 2) (sixConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 2) (sixConfig 5) ^ 2 = 3 - Real.sqrt 6 := by
  left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_two, sixConfig_five, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_34 :
    dist (sixConfig 3) (sixConfig 4) ^ 2 = 3 ∨
    dist (sixConfig 3) (sixConfig 4) ^ 2 = 6 ∨
    dist (sixConfig 3) (sixConfig 4) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 3) (sixConfig 4) ^ 2 = 3 - Real.sqrt 6 := by
  right; left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_three, sixConfig_four, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_35 :
    dist (sixConfig 3) (sixConfig 5) ^ 2 = 3 ∨
    dist (sixConfig 3) (sixConfig 5) ^ 2 = 6 ∨
    dist (sixConfig 3) (sixConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 3) (sixConfig 5) ^ 2 = 3 - Real.sqrt 6 := by
  right; left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_three, sixConfig_five, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

private theorem six_dist_45 :
    dist (sixConfig 4) (sixConfig 5) ^ 2 = 3 ∨
    dist (sixConfig 4) (sixConfig 5) ^ 2 = 6 ∨
    dist (sixConfig 4) (sixConfig 5) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig 4) (sixConfig 5) ^ 2 = 3 - Real.sqrt 6 := by
  right; left
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sixConfig_four, sixConfig_five, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  norm_num
  all_goals nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
    sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]

end PairDistances

set_option maxHeartbeats 800000 in
/-- **Every pairwise squared distance of `sixConfig` is `3`, `6`, `3 + √6`, or
`3 − √6`.**  Assembled from the fifteen per-pair lemmas; the transposed pairs
reduce to them by `dist_comm`. -/
theorem sixConfig_dist_sq {i j : Fin 6} (hij : i ≠ j) :
    dist (sixConfig i) (sixConfig j) ^ 2 = 3 ∨
    dist (sixConfig i) (sixConfig j) ^ 2 = 6 ∨
    dist (sixConfig i) (sixConfig j) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig i) (sixConfig j) ^ 2 = 3 - Real.sqrt 6 := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact six_dist_01
    | exact six_dist_02
    | exact six_dist_03
    | exact six_dist_04
    | exact six_dist_05
    | exact six_dist_12
    | exact six_dist_13
    | exact six_dist_14
    | exact six_dist_15
    | exact six_dist_23
    | exact six_dist_24
    | exact six_dist_25
    | exact six_dist_34
    | exact six_dist_35
    | exact six_dist_45
    | (rw [dist_comm]
       first
       | exact six_dist_01
       | exact six_dist_02
       | exact six_dist_03
       | exact six_dist_04
       | exact six_dist_05
       | exact six_dist_12
       | exact six_dist_13
       | exact six_dist_14
       | exact six_dist_15
       | exact six_dist_23
       | exact six_dist_24
       | exact six_dist_25
       | exact six_dist_34
       | exact six_dist_35
       | exact six_dist_45)

/-- **Every pairwise distance of `sixConfig` lies in
`{√3, √6, √(3+√6), √(3−√6)}`.**  Nonnegative square roots of
`sixConfig_dist_sq`. -/
theorem sixConfig_dist_mem {i j : Fin 6} (hij : i ≠ j) :
    dist (sixConfig i) (sixConfig j) ∈
      ({Real.sqrt 3, Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
        Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ) := by
  have hd0 : 0 ≤ dist (sixConfig i) (sixConfig j) := dist_nonneg
  rcases sixConfig_dist_sq hij with h | h | h | h
  · have he : dist (sixConfig i) (sixConfig j) = Real.sqrt 3 := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]
  · have he : dist (sixConfig i) (sixConfig j) = Real.sqrt 6 := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]
  · have he : dist (sixConfig i) (sixConfig j) = Real.sqrt (3 + Real.sqrt 6) := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]
  · have he : dist (sixConfig i) (sixConfig j) = Real.sqrt (3 - Real.sqrt 6) := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]

/-- The six points are distinct: every pairwise distance lies in a set of four
positive reals, so it never vanishes. -/
theorem sixConfig_injective : Function.Injective sixConfig := by
  intro i j hij
  by_contra hne
  have hmem := sixConfig_dist_mem hne
  rw [hij, dist_self] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hp1 : (0 : ℝ) < Real.sqrt (3 + Real.sqrt 6) :=
    Real.sqrt_pos.mpr (by positivity)
  have hp2 : (0 : ℝ) < Real.sqrt (3 - Real.sqrt 6) :=
    Real.sqrt_pos.mpr (by linarith [sqrt_six_lt])
  rcases hmem with h | h | h | h
  · linarith [sqrt_three_pos]
  · linarith [sqrt_six_pos]
  · linarith [hp1]
  · linarith [hp2]

/-! ## No three collinear: 20 numeric line determinants -/

section NoLine

private theorem six_noLine_012 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_two]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_013 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_three]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_014 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_015 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_023 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_two, sixConfig_three]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_024 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_two, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_025 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_two, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_034 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_three, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_035 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_three, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_045 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_zero, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_123 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_one, sixConfig_two, sixConfig_three]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_124 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_one, sixConfig_two, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_125 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_one, sixConfig_two, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_134 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_one, sixConfig_three, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_135 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_one, sixConfig_three, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_145 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_one, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_234 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_two, sixConfig_three, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_235 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_two, sixConfig_three, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_245 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_two, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noLine_345 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 3 0) + b * (sixConfig 3 1) + c = 0 ∧
      a * (sixConfig 4 0) + b * (sixConfig 4 1) + c = 0 ∧
      a * (sixConfig 5 0) + b * (sixConfig 5 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig_three, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

end NoLine

set_option maxHeartbeats 3200000 in
/-- **No three of the six points are collinear.**  Every genuine index triple
dispatches (via `assumption`, so in any order) to one of the twenty per-triple
line-determinant lemmas. -/
theorem noThreeCollinear_sixConfig : NoThreeCollinear sixConfig := by
  intro i j k hcard
  rintro ⟨a, b, c, hne, e1, e2, e3⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | exact six_noLine_012 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_013 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_014 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_015 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_023 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_024 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_025 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_034 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_035 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_045 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_123 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_124 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_125 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_134 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_135 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_145 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_234 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_235 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_245 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩
    | exact six_noLine_345 ⟨a, b, c, hne, by assumption, by assumption, by assumption⟩

/-! ## No four concyclic: 15 numeric circle determinants -/

section NoCircle

private theorem six_noCircle_0123 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 1) = ρ ∧
      dist center (sixConfig 2) = ρ ∧ dist center (sixConfig 3) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_two, sixConfig_three]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_0124 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 1) = ρ ∧
      dist center (sixConfig 2) = ρ ∧ dist center (sixConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_two, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_0125 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 1) = ρ ∧
      dist center (sixConfig 2) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_two, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_0134 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 1) = ρ ∧
      dist center (sixConfig 3) = ρ ∧ dist center (sixConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_three, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_0135 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 1) = ρ ∧
      dist center (sixConfig 3) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_three, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_0145 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 1) = ρ ∧
      dist center (sixConfig 4) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_one, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_0234 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 2) = ρ ∧
      dist center (sixConfig 3) = ρ ∧ dist center (sixConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_two, sixConfig_three, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_0235 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 2) = ρ ∧
      dist center (sixConfig 3) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_two, sixConfig_three, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_0245 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 2) = ρ ∧
      dist center (sixConfig 4) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_two, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_0345 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 0) = ρ ∧ dist center (sixConfig 3) = ρ ∧
      dist center (sixConfig 4) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_zero, sixConfig_three, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_1234 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 1) = ρ ∧ dist center (sixConfig 2) = ρ ∧
      dist center (sixConfig 3) = ρ ∧ dist center (sixConfig 4) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_one, sixConfig_two, sixConfig_three, sixConfig_four]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_1235 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 1) = ρ ∧ dist center (sixConfig 2) = ρ ∧
      dist center (sixConfig 3) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_one, sixConfig_two, sixConfig_three, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_1245 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 1) = ρ ∧ dist center (sixConfig 2) = ρ ∧
      dist center (sixConfig 4) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_one, sixConfig_two, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_1345 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 1) = ρ ∧ dist center (sixConfig 3) = ρ ∧
      dist center (sixConfig 4) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_one, sixConfig_three, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

private theorem six_noCircle_2345 :
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ),
      dist center (sixConfig 2) = ρ ∧ dist center (sixConfig 3) = ρ ∧
      dist center (sixConfig 4) = ρ ∧ dist center (sixConfig 5) = ρ := by
  apply not_concyclic_of_det
  simp only [sixConfig_two, sixConfig_three, sixConfig_four, sixConfig_five]
  norm_num
  all_goals intro heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

end NoCircle

set_option maxHeartbeats 4000000 in
/-- **No four of the six points are concyclic.**  Every genuine index quadruple
dispatches (via `assumption`, so in any order) to one of the fifteen per-quadruple
circle-determinant lemmas. -/
theorem noFourConcyclic_sixConfig : NoFourConcyclic sixConfig := by
  intro a b c d hcard
  rintro ⟨center, ρ, h1, h2, h3, h4⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact six_noCircle_0123
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_0124
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_0125
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_0134
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_0135
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_0145
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_0234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_0235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_0245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_0345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_1234
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_1235
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_1245
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_1345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩
    | exact six_noCircle_2345
        ⟨center, ρ, by assumption, by assumption, by assumption, by assumption⟩

/-- **`sixConfig` is in general position.** -/
theorem inGeneralPosition_sixConfig : InGeneralPosition sixConfig :=
  ⟨sixConfig_injective, noThreeCollinear_sixConfig, noFourConcyclic_sixConfig⟩

/-- **`sixConfig` realizes at most four distinct distances.**  Every positive
pairwise distance lies in the four-element set `{√3, √6, √(3+√6), √(3−√6)}`
(`sixConfig_dist_mem`), so the distinct-distance count is at most `4`. -/
theorem numDistinctDistances_sixConfig_le :
    numDistinctDistances sixConfig ≤ 4 := by
  unfold numDistinctDistances
  have hsub :
      ((univ.product univ).image
          (fun p : Fin 6 × Fin 6 =>
            dist (sixConfig p.1) (sixConfig p.2))).filter (· > 0)
        ⊆ ({Real.sqrt 3, Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
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
    exact sixConfig_dist_mem hne
  calc (((univ.product univ).image
          (fun p : Fin 6 × Fin 6 =>
            dist (sixConfig p.1) (sixConfig p.2))).filter (· > 0)).card
      ≤ ({Real.sqrt 3, Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
          Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card := card_le_card hsub
    _ ≤ ({Real.sqrt 6, Real.sqrt (3 + Real.sqrt 6),
          Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card + 1 := card_insert_le _ _
    _ ≤ (({Real.sqrt (3 + Real.sqrt 6),
          Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card + 1) + 1 :=
        Nat.add_le_add_right (card_insert_le _ _) 1
    _ ≤ ((({Real.sqrt (3 - Real.sqrt 6)} : Finset ℝ).card + 1) + 1) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_right (card_insert_le _ _) 1) 1
    _ = 4 := by simp

/-! ## The bounds -/

/-- **`h 6 ≤ 4`.**  The explicit general-position four-distance witness
`sixConfig` caps the minimum.  Before this theorem the best upper bound was the
generic `h 6 ≤ 15` from `h_le_choose_two`. -/
theorem h_six_le_four : h 6 ≤ 4 :=
  le_trans (h_le_of_inGeneralPosition inGeneralPosition_sixConfig)
    numDistinctDistances_sixConfig_le

/-- **`3 ≤ h 6 ≤ 4`.**  Lower bound from `h 5 = 3` and monotonicity
(`three_le_h_six`, in `Erdos98WIP01Thresholds`); upper bound from `sixConfig`. -/
theorem h_six_bounds : 3 ≤ h 6 ∧ h 6 ≤ 4 :=
  ⟨three_le_h_six, h_six_le_four⟩

/-- **The six-point dichotomy: `h 6 = 3` or `h 6 = 4`.**  Deciding which is the
open remainder: `h 6 = 3` iff a general-position 6-point THREE-distance
configuration exists (a question the blocked-route registry records as open);
otherwise `h 6 = 4` exactly. -/
theorem h_six_eq_three_or_four : h 6 = 3 ∨ h 6 = 4 := by
  have h1 := three_le_h_six
  have h2 := h_six_le_four
  omega

end Erdos98WIP01
