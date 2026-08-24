import Proofs.Erdos85ConnectedDefectAmbientFork
import Proofs.Erdos85TwoSeparatorMantelContradiction

/-!
# Routing a defect fork after deleting its center and branch

Once every two-vertex deletion of the connected defect graph is connected,
the two outer tips of an ambient fork can be joined while avoiding both the
fork center and its distinguished branch vertex.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Two vertices distinct from `x,y` become a reachable pair in the induced
graph obtained by deleting `x,y`. -/
theorem exists_twoDeleted_subtypes_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (x y z w : V)
    (hxz : x ≠ z) (hyz : y ≠ z) (hxw : x ≠ w) (hyw : y ≠ w)
    (hconn : (D.induce
      (↑(Finset.univ \ ({x, y} : Finset V)) : Set V)).Connected) :
    ∃ (z' w' : (↑(Finset.univ \ ({x, y} : Finset V)) : Set V)),
      z'.1 = z ∧ w'.1 = w ∧
      (D.induce (↑(Finset.univ \ ({x, y} : Finset V)) : Set V)).Reachable
        z' w' := by
  let U : Set V := ↑(Finset.univ \ ({x, y} : Finset V))
  have hzU : z ∈ U := by
    simp only [U, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
      not_or]
    exact ⟨hxz.symm, hyz.symm⟩
  have hwU : w ∈ U := by
    simp only [U, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
      not_or]
    exact ⟨hxw.symm, hyw.symm⟩
  let z' : U := ⟨z, hzU⟩
  let w' : U := ⟨w, hwU⟩
  refine ⟨z', w', rfl, rfl, ?_⟩
  exact hconn.preconnected z' w'

/-- Fork-shaped specialization: adjacency to `x` supplies distinctness from
`x`, while the explicit fork noncoincidences supply distinctness from `y`. -/
theorem ambientFork_tips_reachable_in_twoDeletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (x y z w : V)
    (hxz : D.Adj x z) (hxw : D.Adj x w)
    (hyz : y ≠ z) (hyw : y ≠ w)
    (hconn : (D.induce
      (↑(Finset.univ \ ({x, y} : Finset V)) : Set V)).Connected) :
    ∃ (z' w' : (↑(Finset.univ \ ({x, y} : Finset V)) : Set V)),
      z'.1 = z ∧ w'.1 = w ∧
      (D.induce (↑(Finset.univ \ ({x, y} : Finset V)) : Set V)).Reachable
        z' w' := by
  exact exists_twoDeleted_subtypes_reachable D x y z w
    (D.ne_of_adj hxz) hyz (D.ne_of_adj hxw) hyw hconn

/-- In the dyadic connected binary-square branch with `q ≥ 8`, there is a
defect fork whose two outer tips remain connected after deleting the center
and the distinguished branch vertex. -/
theorem connected_binarySquare_dyadic_exists_defectFork_reachable_after_delete_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k r : ℕ}
    (hq8 : 8 ≤ q) (hqpow : q = 2 ^ k)
    (hr : 2 ≤ r) (hqeven : q = 2 * (r + 1))
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    ∃ x y z w : V,
      (secondOrderDefectGraph G).Adj x y ∧
      (secondOrderDefectGraph G).Adj x z ∧
      (secondOrderDefectGraph G).Adj x w ∧
      ¬ (secondOrderDefectGraph G).Adj y z ∧
      ¬ (secondOrderDefectGraph G).Adj y w ∧
      y ≠ z ∧ y ≠ w ∧ z ≠ w ∧
      ∃ (z' w' : (↑(Finset.univ \ ({x, y} : Finset V)) : Set V)),
        z'.1 = z ∧ w'.1 = w ∧
        ((secondOrderDefectGraph G).induce
          (↑(Finset.univ \ ({x, y} : Finset V)) : Set V)).Reachable z' w' := by
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hyzNe, hywNe, hzw⟩ :=
    connected_binarySquare_dyadic_exists_ambient_defectFork
      G hfree (by omega : 3 ≤ q) hqpow hreg hcard hDconn
  have hWcard : ({x, y} : Finset V).card = 2 := by
    simp [hxy.ne]
  have hdelete := binarySquare_connected_secondOrderDefect_delete_two_connected
    G hfree hq8 hr hqeven hreg hcard hDconn ({x, y} : Finset V) hWcard
  obtain ⟨z', w', hz', hw', hreach⟩ :=
    ambientFork_tips_reachable_in_twoDeletion
      (secondOrderDefectGraph G) x y z w hxz hxw hyzNe hywNe hdelete
  exact ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hyzNe, hywNe, hzw,
    z', w', hz', hw', hreach⟩

#print axioms exists_twoDeleted_subtypes_reachable
#print axioms ambientFork_tips_reachable_in_twoDeletion
#print axioms connected_binarySquare_dyadic_exists_defectFork_reachable_after_delete_two

end

end Erdos85
