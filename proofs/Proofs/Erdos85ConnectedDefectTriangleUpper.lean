import Proofs.Erdos85ConnectedDefectLocalTriangleDeficit

/-!
# Global defect-triangle upper bound from strict cut energy

Summing the exact closed-star cut identity counts every defect triangle at
its three vertices.  A strict lower bound on total cut mass therefore gives
a strict upper bound on the total number of defect triangles.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- Generic conversion from strict closed-star cut mass to a global triangle
upper bound.  The subtraction-free form is robust over naturals. -/
theorem six_mul_cliques_add_excess_add_four_cube_le_fourth_add_two_square
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (q c : ℕ) (hq : 1 ≤ q) (hcard : Fintype.card V = q * q)
    (hreg : ∀ x, D.degree x = q - 1)
    (hstrict : q * q * q + c ≤ ∑ x : V,
      finsetGraphCutSize D (insert x (D.neighborFinset x))) :
    6 * (D.cliqueFinset 3).card + c + 4 * (q * q * q) ≤
      q * q * q * q + 2 * (q * q) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, q = r + 1 := ⟨q - 1, by omega⟩
  let t : V → ℕ := fun x =>
    (D.induce (D.neighborSet x)).edgeFinset.card
  have hsum :
      (∑ x : V, (finsetGraphCutSize D (insert x (D.neighborFinset x)) +
        (2 * r + 2 * t x))) =
      ∑ x : V, (r + 1) * r := by
    apply Finset.sum_congr rfl
    intro x _
    simpa using
      (closedNeighborhood_cut_add_two_mul_degree_add_two_mul_localEdges
        D hreg x)
  have ht : (∑ x : V, t x) = 3 * (D.cliqueFinset 3).card := by
    exact sum_localEdges_eq_three_mul_cliques D
  simp only [Finset.sum_add_distrib, Finset.sum_const] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  simp [hcard] at hsum
  rw [ht] at hsum
  nlinarith [hsum, hstrict]

/-- Connected binary-square data in residue class one satisfies the strict
global defect-triangle census. -/
theorem connected_binarySquare_defectTriangles_upper_of_mod_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqeven : Even q) (hqmod : q % 3 = 1)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    6 * ((secondOrderDefectGraph G).cliqueFinset 3).card + 2 +
        4 * (q * q * q) ≤ q * q * q * q + 2 * (q * q) := by
  obtain ⟨hDreg, hcut⟩ :=
    connected_binarySquare_defectReg_and_closedStarCut_pred_le
      G hfree hq hreg hcard hDconn
  have hstrict :=
    binarySquare_regular_closedStarCut_energy_ge_cube_add_two_of_cut_pred_le
      G (by omega) hqeven hcard hDreg hcut hqmod
  exact six_mul_cliques_add_excess_add_four_cube_le_fourth_add_two_square
    (secondOrderDefectGraph G) q 2 (by omega) hcard hDreg hstrict

/-- Connected binary-square data in residue class two gains four units in
the global defect-triangle census. -/
theorem connected_binarySquare_defectTriangles_upper_of_mod_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqeven : Even q) (hqmod : q % 3 = 2)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    6 * ((secondOrderDefectGraph G).cliqueFinset 3).card + 4 +
        4 * (q * q * q) ≤ q * q * q * q + 2 * (q * q) := by
  obtain ⟨hDreg, hcut⟩ :=
    connected_binarySquare_defectReg_and_closedStarCut_pred_le
      G hfree hq hreg hcard hDconn
  have hstrict :=
    binarySquare_regular_closedStarCut_energy_ge_cube_add_four_of_cut_pred_le
      G (by omega) hqeven hcard hDreg hcut hqmod
  exact six_mul_cliques_add_excess_add_four_cube_le_fourth_add_two_square
    (secondOrderDefectGraph G) q 4 (by omega) hcard hDreg hstrict

/-- Uniform dyadic global defect-triangle upper bound. -/
theorem connected_binarySquare_dyadic_defectTriangles_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 3 ≤ q)
    (hqpow : q = 2 ^ k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    6 * ((secondOrderDefectGraph G).cliqueFinset 3).card + 2 +
        4 * (q * q * q) ≤ q * q * q * q + 2 * (q * q) := by
  have hqeven := even_of_three_le_of_eq_two_pow hq hqpow
  rcases two_pow_mod_three_eq_one_or_two k with hmod | hmod
  · apply connected_binarySquare_defectTriangles_upper_of_mod_one
      G hfree hq hqeven
    · simpa [hqpow] using hmod
    · exact hreg
    · exact hcard
    · exact hDconn
  · have hstrong := connected_binarySquare_defectTriangles_upper_of_mod_two
      G hfree hq hqeven (by simpa [hqpow] using hmod) hreg hcard hDconn
    omega

end

end Erdos85

#print axioms Erdos85.six_mul_cliques_add_excess_add_four_cube_le_fourth_add_two_square
#print axioms Erdos85.connected_binarySquare_defectTriangles_upper_of_mod_one
#print axioms Erdos85.connected_binarySquare_defectTriangles_upper_of_mod_two
#print axioms Erdos85.connected_binarySquare_dyadic_defectTriangles_upper
