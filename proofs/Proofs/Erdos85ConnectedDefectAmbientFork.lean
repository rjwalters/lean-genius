import Proofs.Erdos85ConnectedDefectNeighborhoodFork

/-!
# An ambient four-vertex defect fork

The local missing-pair theorem is stated as a complement-degree bound in an
induced-neighborhood subtype.  Here it is unpacked into four ambient vertices
and literal defect adjacency/nonadjacency relations.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Unpack complement degree at least two inside a neighborhood into two
distinct ambient neighbors that are both nonadjacent to the center vertex. -/
theorem exists_ambient_fork_of_inducedNeighborhood_compl_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (x : V)
    (y : D.neighborSet x)
    (hy : 2 ≤ ((D.induce (D.neighborSet x))ᶜ).degree y) :
    ∃ z w : V,
      D.Adj x z ∧ D.Adj x w ∧
      ¬ D.Adj y.1 z ∧ ¬ D.Adj y.1 w ∧
      y.1 ≠ z ∧ y.1 ≠ w ∧ z ≠ w := by
  classical
  let H := (D.induce (D.neighborSet x))ᶜ
  change 2 ≤ H.degree y at hy
  have hcard : 1 < (H.neighborFinset y).card := by
    rw [H.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.mp hcard
  have hyzC : H.Adj y z := (H.mem_neighborFinset y z).mp hz
  have hywC : H.Adj y w := (H.mem_neighborFinset y w).mp hw
  have hzN : D.Adj x z.1 := z.2
  have hwN : D.Adj x w.1 := w.2
  have hyzNe : y ≠ z := H.ne_of_adj hyzC
  have hywNe : y ≠ w := H.ne_of_adj hywC
  have hyzNot : ¬ D.Adj y.1 z.1 := by
    intro hyz
    have : (D.induce (D.neighborSet x)).Adj y z := hyz
    exact hyzC.2 this
  have hywNot : ¬ D.Adj y.1 w.1 := by
    intro hyw
    have : (D.induce (D.neighborSet x)).Adj y w := hyw
    exact hywC.2 this
  refine ⟨z.1, w.1, hzN, hwN, hyzNot, hywNot, ?_, ?_, ?_⟩
  · exact fun h => hyzNe (Subtype.ext h)
  · exact fun h => hywNe (Subtype.ext h)
  · exact fun h => hzw (Subtype.ext h)

/-- The connected dyadic defect branch contains an explicit ambient fork:
three distinct neighbors `y,z,w` of `x`, with `y` nonadjacent to both `z`
and `w` in the defect graph. -/
theorem connected_binarySquare_dyadic_exists_ambient_defectFork
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 3 ≤ q)
    (hqpow : q = 2 ^ k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    ∃ x y z w : V,
      (secondOrderDefectGraph G).Adj x y ∧
      (secondOrderDefectGraph G).Adj x z ∧
      (secondOrderDefectGraph G).Adj x w ∧
      ¬ (secondOrderDefectGraph G).Adj y z ∧
      ¬ (secondOrderDefectGraph G).Adj y w ∧
      y ≠ z ∧ y ≠ w ∧ z ≠ w := by
  let D := secondOrderDefectGraph G
  obtain ⟨x, y, hy⟩ :=
    connected_binarySquare_dyadic_exists_neighborhood_fork
      G hfree hq hqpow hreg hcard hDconn
  obtain ⟨z, w, hxz, hxw, hyz, hyw, hyzNe, hywNe, hzw⟩ :=
    exists_ambient_fork_of_inducedNeighborhood_compl_degree_two D x y hy
  exact ⟨x, y.1, z, w, y.2, hxz, hxw, hyz, hyw, hyzNe, hywNe, hzw⟩

#print axioms exists_ambient_fork_of_inducedNeighborhood_compl_degree_two
#print axioms connected_binarySquare_dyadic_exists_ambient_defectFork

end

end Erdos85
