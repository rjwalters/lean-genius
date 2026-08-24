import Proofs.Erdos85ConnectedDefectAmbientFork

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

#print axioms exists_twoDeleted_subtypes_reachable
#print axioms ambientFork_tips_reachable_in_twoDeletion

end

end Erdos85
