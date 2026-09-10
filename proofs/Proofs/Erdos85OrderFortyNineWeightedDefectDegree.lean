import Proofs.Erdos85SquareOrderHighIncidence
import Proofs.Erdos85DegreeExcessStratification

/-! Actual order49 degree sums used by the nonregular fifth-trace identity.
The standard tight-edge-cover premise is retained explicitly. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
  (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
  (hcard : Fintype.card V = 49)

include hfree hmin hcover hcard

/-- Total defect degree is294 minus14 per high vertex. -/
theorem orderFortyNine_sum_defectDegree_add_fourteen_high :
    (∑ x : V, (secondOrderDefectGraph G).degree x) +
      14 * (squareOrderHighVertices G 7).card = 294 := by
  have hex := squareOrder_sum_degreeExcess_eq_card_high G hfree
    (d := 7) (by norm_num) hmin hcover (by simpa using hcard)
  have hterm (x : V) : (G.degree x-7)*(7-1)+G.degree x*(G.degree x-7) =
      14*(G.degree x-7) := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover G hfree
      (d := 7) (by norm_num) hmin hcover (by simpa using hcard) x with hx | hx <;>
      simp [hx]
  have h := sum_defectDegree_add_sum_weightedDegreeExcess_eq_card_mul_orderExcess
    G hfree (d := 7) (q := 6) (by norm_num) hmin (by simpa using hcard)
  simp_rw [hterm] at h
  rw [← Finset.mul_sum, hex, hcard] at h
  exact h

/-- Weighting by original degree multiplies the defect degree sum by7,
since every degree8 vertex is isolated in the defect graph. -/
theorem orderFortyNine_sum_degree_mul_defectDegree :
    (∑ x : V, (G.degree x : ℤ) * ((secondOrderDefectGraph G).degree x : ℤ)) =
      2058 - 98 * ((squareOrderHighVertices G 7).card : ℤ) := by
  have hpoint (x : V) : (G.degree x : ℤ) * ((secondOrderDefectGraph G).degree x : ℤ) =
      7 * ((secondOrderDefectGraph G).degree x : ℤ) := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover G hfree
      (d := 7) (by norm_num) hmin hcover (by simpa using hcard) x with hx | hx
    · simp [hx]
    · have hz := (squareOrder_degree_succ_highRoot_structure G hfree
        (d := 7) (by norm_num) hmin (by simpa using hcard) hx).1
      simp [hz]
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  have h := orderFortyNine_sum_defectDegree_add_fourteen_high G hfree hmin hcover hcard
  have hi : (∑ x : V, ((secondOrderDefectGraph G).degree x : ℤ)) +
      14 * ((squareOrderHighVertices G 7).card : ℤ) = 294 := by exact_mod_cast h
  linarith
/-- Original degree sum at order49. -/
theorem orderFortyNine_sum_degree_eq_cube_add_high :
    (∑ x : V, (G.degree x : ℤ)) = 343 + ((squareOrderHighVertices G 7).card : ℤ) := by
  have hex := squareOrder_sum_degreeExcess_eq_card_high G hfree
    (d := 7) (by norm_num) hmin hcover (by simpa using hcard)
  have hexi : (∑ x : V, ((G.degree x-7 : ℕ) : ℤ)) =
      ((squareOrderHighVertices G 7).card : ℤ) := by exact_mod_cast hex
  have hterm (x : V) : (G.degree x : ℤ) = 7 + ((G.degree x-7 : ℕ) : ℤ) := by
    have h := Nat.sub_add_cancel (hmin x)
    omega
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, hexi]
  norm_num

/-- Degree times predecessor sum needed for the nonregular fifth trace. -/
theorem orderFortyNine_sum_degree_mul_pred :
    (∑ x : V, (G.degree x : ℤ) * ((G.degree x : ℤ)-1)) =
      2058 + 14 * ((squareOrderHighVertices G 7).card : ℤ) := by
  have hex := squareOrder_sum_degreeExcess_eq_card_high G hfree
    (d := 7) (by norm_num) hmin hcover (by simpa using hcard)
  have hexi : (∑ x : V, ((G.degree x-7 : ℕ) : ℤ)) =
      ((squareOrderHighVertices G 7).card : ℤ) := by exact_mod_cast hex
  have hterm (x : V) : (G.degree x : ℤ) * ((G.degree x : ℤ)-1) =
      42 + 14 * ((G.degree x-7 : ℕ) : ℤ) := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover G hfree
      (d := 7) (by norm_num) hmin hcover (by simpa using hcard) x with hx | hx <;>
      norm_num [hx]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard,
    ← Finset.mul_sum, hexi]
  norm_num
end Erdos85
