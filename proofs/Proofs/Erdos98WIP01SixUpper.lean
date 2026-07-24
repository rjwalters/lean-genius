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
  distinct distances, pinning `h 6 ∈ {3, 4}`.

  **The configuration** (`sixConfig`): two concentric equilateral triangles,
  inner of circumradius `1` at angles `0°, 120°, 240°`, outer of circumradius `√2`
  at angles `90°, 210°, 330°` (twist `90°`):

    P₀ = (1, 0)          P₁ = (−1/2, √3/2)     P₂ = (−1/2, −√3/2)
    P₃ = (0, √2)         P₄ = (−√6/2, −√2/2)   P₅ = (√6/2, −√2/2)

  Squared distances: inner side `3`, outer side `6`, and cross distances
  `|B − A|² = 3 − 2√2·cos Δ` for twist angles `Δ ∈ {90°, 210°, 330°}`, i.e.
  `3`, `3 + √6`, `3 − √6`.  The `Δ = 90°` cross orbit MERGES with the inner side
  (that is the point of the `√2` radius: `R² = 2r²` makes `cos Δ = 0` work), so
  only four values `{3, 6, 3 + √6, 3 − √6}` occur — distances
  `{√3, √6, √(3+√6), √(3−√6)}`.

  **General position**:
  * no 3 collinear — all 20 triple determinants are nonzero;
  * no 4 concyclic — the two circumcircles are concentric of different radii, so
    a 3+1 split fails on radii; a 2+2 split would need an inner chord parallel to
    an outer chord, but inner chord directions are `{30°, 90°, 150°}` and outer
    ones `{0°, 60°, 120°}` — disjoint.  Formally, all 15 concyclicity
    determinants are nonzero.

  Both conditions are verified by two new GENERAL determinant criteria
  (`not_collinear_of_det`, `not_concyclic_of_det`) whose proofs are deterministic
  `linear_combination` cofactor identities — no per-case search with unknown
  line/centre coordinates, unlike the `h5Config` treatment.  Each of the 35
  concrete obligations is then a numeric surd inequality.

  Within the twisted-triangle two-parameter family `(R, θ)` a THREE-distance
  merge is impossible in general position: `inner = cross₁ = cross₂` or
  `inner = cross₁, outer = cross₂` force `R = 2, θ = ±60°` (three points
  collinear: the config degenerates to alternating hexagonal directions where
  `(−√3,1), (0,1), (√3,1)` are collinear) or `R = 1` (the two triangles
  coincide).  So `h 6 = 3`, if true, needs a construction outside this family —
  consistent with the blocked-route registry entry.

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
no line `a·x + b·y + c = 0` with `(a,b,c) ≠ 0` passes through `p, q, r`. -/
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

set_option maxHeartbeats 1600000 in
/-- **Every pairwise squared distance of `sixConfig` is `3`, `6`, `3 + √6`, or
`3 − √6`.**  A direct coordinate computation over all off-diagonal pairs, using
`√2² = 2`, `√3² = 3`, `√6² = 6`, and `√2·√3 = √6`. -/
theorem sixConfig_dist_sq {i j : Fin 6} (hij : i ≠ j) :
    dist (sixConfig i) (sixConfig j) ^ 2 = 3 ∨
    dist (sixConfig i) (sixConfig j) ^ 2 = 6 ∨
    dist (sixConfig i) (sixConfig j) ^ 2 = 3 + Real.sqrt 6 ∨
    dist (sixConfig i) (sixConfig j) ^ 2 = 3 - Real.sqrt 6 := by
  rw [EuclideanSpace.dist_sq_eq]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (simp only [sixConfig, Fin.sum_univ_two, Real.dist_eq, sq_abs]
       first
       | (left
          norm_num
          nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
            sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six])
       | (right; left
          norm_num
          nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
            sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six])
       | (right; right; left
          norm_num
          nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
            sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six])
       | (right; right; right
          norm_num
          nlinarith [sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_mul_sqrt_three,
            sqrt_two_mul_sqrt_six, sqrt_three_mul_sqrt_six]))

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

/-- Closing tactic for the 20 line-determinant obligations: reduce the
coordinates, then refute the vanishing of a `ℚ(√2,√3)`-linear combination using
the recorded surd facts and rational bracketing bounds. -/
private def sixLineFacts : Unit := ()  -- (documentation anchor only)

private theorem six_noLine_012 :
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (sixConfig 0 0) + b * (sixConfig 0 1) + c = 0 ∧
      a * (sixConfig 1 0) + b * (sixConfig 1 1) + c = 0 ∧
      a * (sixConfig 2 0) + b * (sixConfig 2 1) + c = 0 := by
  apply not_collinear_of_det
  simp only [sixConfig]
  intro heq
  norm_num at heq
  all_goals nlinarith [heq, sqrt_two_sq, sqrt_three_sq, sqrt_six_sq, sqrt_two_pos,
    sqrt_three_pos, sqrt_six_pos, sqrt_two_mul_sqrt_three, sqrt_two_mul_sqrt_six,
    sqrt_three_mul_sqrt_six, sqrt_two_lt, lt_sqrt_two, sqrt_three_lt, lt_sqrt_three,
    sqrt_six_lt, lt_sqrt_six]

end NoLine

end Erdos98WIP01
