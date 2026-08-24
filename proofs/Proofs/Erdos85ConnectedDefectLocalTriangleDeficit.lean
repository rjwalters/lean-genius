import Proofs.Erdos85ConnectedIncidenceBottleneckStrictResidue
import Proofs.Erdos85ConnectedIncidenceBottleneckDyadicStrict

/-!
# A low local-triangle vertex in the connected defect branch

Strict global closed-star cut energy forces one cut to exceed its even
baseline by at least two.  The exact closed-neighborhood identity converts
that cut excess into a concrete deficit in the number of edges induced by a
defect neighborhood.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- An even-valued family whose total exceeds the even constant baseline by
two has a coordinate at least two above baseline. -/
theorem exists_add_two_le_of_even_sum_ge_card_mul_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (δ : V → ℕ) (hqeven : Even q)
    (hδeven : ∀ x, Even (δ x))
    (hsum : Fintype.card V * q + 2 ≤ ∑ x, δ x) :
    ∃ x, q + 2 ≤ δ x := by
  by_contra hnot
  push Not at hnot
  have hpoint : ∀ x, δ x ≤ q := by
    intro x
    obtain ⟨a, ha⟩ := hqeven
    obtain ⟨b, hb⟩ := hδeven x
    have hx := hnot x
    omega
  have hupper := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun x _ => hpoint x)
  have hupper' : (∑ x, δ x) ≤ Fintype.card V * q := by
    simpa [nsmul_eq_mul] using hupper
  omega

/-- A strict closed-star cut sum produces a vertex whose induced
neighborhood has the corresponding doubled edge deficit. -/
theorem exists_localEdges_deficit_of_strict_closedStarCut_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (q : ℕ) (hq : 1 ≤ q) (hqeven : Even q)
    (hcard : Fintype.card V = q * q)
    (hreg : ∀ x, D.degree x = q - 1)
    (hsum : q * q * q + 2 ≤ ∑ x : V,
      finsetGraphCutSize D (insert x (D.neighborFinset x))) :
    ∃ x : V,
      2 * (D.induce (D.neighborSet x)).edgeFinset.card + 4 * q ≤ q * q := by
  have hcutEven : ∀ x : V,
      Even (finsetGraphCutSize D (insert x (D.neighborFinset x))) := by
    intro x
    let S := insert x (D.neighborFinset x)
    have hScard : S.card = q := by
      simp [S, hreg x]
      omega
    have hprod : Even ((q - 1) * S.card) := by
      rw [hScard]
      exact hqeven.mul_left (q - 1)
    exact even_finsetGraphCutIncidenceCount_of_regular_product_even
      D S (q - 1) hreg hprod
  have hsum' : Fintype.card V * q + 2 ≤ ∑ x : V,
      finsetGraphCutSize D (insert x (D.neighborFinset x)) := by
    simpa [hcard, mul_assoc] using hsum
  obtain ⟨x, hx⟩ := exists_add_two_le_of_even_sum_ge_card_mul_add_two
    q (fun x => finsetGraphCutSize D (insert x (D.neighborFinset x)))
    hqeven hcutEven hsum'
  refine ⟨x, ?_⟩
  have hid := closedNeighborhood_cut_add_two_mul_degree_add_two_mul_localEdges
    D hreg x
  rw [Nat.sub_add_cancel hq] at hid
  have hmul : q * (q - 1) + q = q * q := by
    calc
      q * (q - 1) + q = q * ((q - 1) + 1) := by ring
      _ = q * q := by rw [Nat.sub_add_cancel hq]
  omega

/-- Connected binary-square data in residue class one contains a defect
vertex with a low-edge neighborhood. -/
theorem connected_binarySquare_exists_localEdges_deficit_of_mod_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqeven : Even q) (hqmod : q % 3 = 1)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    ∃ x : V, 2 * ((secondOrderDefectGraph G).induce
      ((secondOrderDefectGraph G).neighborSet x)).edgeFinset.card + 4 * q ≤
        q * q := by
  obtain ⟨hDreg, hcut⟩ :=
    connected_binarySquare_defectReg_and_closedStarCut_pred_le
      G hfree hq hreg hcard hDconn
  have hsum :=
    binarySquare_regular_closedStarCut_energy_ge_cube_add_two_of_cut_pred_le
      G (by omega) hqeven hcard hDreg hcut hqmod
  exact exists_localEdges_deficit_of_strict_closedStarCut_sum
    (secondOrderDefectGraph G) q (by omega) hqeven hcard hDreg hsum

/-- Connected binary-square data in residue class two contains a defect
vertex with a low-edge neighborhood. -/
theorem connected_binarySquare_exists_localEdges_deficit_of_mod_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqeven : Even q) (hqmod : q % 3 = 2)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    ∃ x : V, 2 * ((secondOrderDefectGraph G).induce
      ((secondOrderDefectGraph G).neighborSet x)).edgeFinset.card + 4 * q ≤
        q * q := by
  obtain ⟨hDreg, hcut⟩ :=
    connected_binarySquare_defectReg_and_closedStarCut_pred_le
      G hfree hq hreg hcard hDconn
  have hsum4 :=
    binarySquare_regular_closedStarCut_energy_ge_cube_add_four_of_cut_pred_le
      G (by omega) hqeven hcard hDreg hcut hqmod
  have hsum : q * q * q + 2 ≤ ∑ x : V,
      finsetGraphCutSize (secondOrderDefectGraph G)
        (insert x ((secondOrderDefectGraph G).neighborFinset x)) :=
    hsum4.trans' (by omega)
  exact exists_localEdges_deficit_of_strict_closedStarCut_sum
    (secondOrderDefectGraph G) q (by omega) hqeven hcard hDreg hsum

/-- In the actual dyadic connected branch, some defect neighborhood has the
strict local edge deficit, independently of the exponent parity. -/
theorem connected_binarySquare_dyadic_exists_localEdges_deficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 3 ≤ q)
    (hqpow : q = 2 ^ k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    ∃ x : V, 2 * ((secondOrderDefectGraph G).induce
      ((secondOrderDefectGraph G).neighborSet x)).edgeFinset.card + 4 * q ≤
        q * q := by
  have hqeven := even_of_three_le_of_eq_two_pow hq hqpow
  rcases two_pow_mod_three_eq_one_or_two k with hmod | hmod
  · apply connected_binarySquare_exists_localEdges_deficit_of_mod_one
      G hfree hq hqeven
    · simpa [hqpow] using hmod
    · exact hreg
    · exact hcard
    · exact hDconn
  · apply connected_binarySquare_exists_localEdges_deficit_of_mod_two
      G hfree hq hqeven
    · simpa [hqpow] using hmod
    · exact hreg
    · exact hcard
    · exact hDconn

end

end Erdos85

#print axioms Erdos85.exists_add_two_le_of_even_sum_ge_card_mul_add_two
#print axioms Erdos85.exists_localEdges_deficit_of_strict_closedStarCut_sum
#print axioms Erdos85.connected_binarySquare_exists_localEdges_deficit_of_mod_one
#print axioms Erdos85.connected_binarySquare_exists_localEdges_deficit_of_mod_two
#print axioms Erdos85.connected_binarySquare_dyadic_exists_localEdges_deficit
