import Proofs.Erdos85CompensatedRepair
import Proofs.Erdos85RepairSet

/-!
# Regular-witness constraints for compensated repair

In a regular witness, deleting one vertex gives every old neighbor a one-unit
degree defect.  The compensated cross-edge budget therefore permits at most one
such neighbor to lose any additional cross edge.
-/

open SimpleGraph

namespace Erdos85

/-- Neighbors of the deleted vertex that would lose at least one additional
edge in the cross-edge deletion. -/
noncomputable def damagedDeletedNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (S T : Finset {y : V // y ≠ x}) :
    Finset {y : V // y ≠ x} := by
  classical
  exact (deletedNeighborhood G x).filter fun v =>
    1 ≤ crossEdgeLoss (G.induce {y | y ≠ x}) S T v

@[simp] theorem mem_damagedDeletedNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (S T : Finset {y : V // y ≠ x}) (v : {y : V // y ≠ x}) :
    v ∈ damagedDeletedNeighborhood G x S T ↔
      G.Adj v x ∧
      1 ≤ crossEdgeLoss (G.induce {y | y ≠ x}) S T v := by
  classical
  simp [damagedDeletedNeighborhood, mem_deletedNeighborhood]

/-- In a d-regular graph, a valid compensated budget can delete an
additional cross edge at at most one neighbor of the deleted vertex. -/
theorem card_damagedDeletedNeighborhood_le_one_of_regular_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (S T : Finset {y : V // y ≠ x}) {d : ℕ}
    (hd : 1 ≤ d) (hreg : ∀ v, G.degree v = d)
    (hbudget : ∀ v : {y : V // y ≠ x},
      d + crossEdgeLoss (G.induce {y | y ≠ x}) S T v ≤
        (G.induce {y | y ≠ x}).degree v +
          (if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0))
    (hinter : (S ∩ T).card ≤ 1) :
    (damagedDeletedNeighborhood G x S T).card ≤ 1 := by
  apply card_one_defect_pos_loss_le_one
    (damagedDeletedNeighborhood G x S T) S T
    (fun v => (G.induce {y | y ≠ x}).degree v)
    (fun v => crossEdgeLoss (G.induce {y | y ≠ x}) S T v) hd
  · intro v hv
    have hvx := (mem_damagedDeletedNeighborhood G x S T v).mp hv |>.1
    rw [degree_induce_delete_eq, hreg]
    simp [hvx]
  · intro v _
    exact hbudget v
  · intro v hv
    exact (mem_damagedDeletedNeighborhood G x S T v).mp hv |>.2
  · exact hinter

/-- In the regular case the two attachment sets must cover the entire deleted
neighborhood. -/
theorem deletedNeighborhood_subset_union_of_regular_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (S T : Finset {y : V // y ≠ x}) {d : ℕ}
    (hd : 1 ≤ d) (hreg : ∀ v, G.degree v = d)
    (hbudget : ∀ v : {y : V // y ≠ x},
      d + crossEdgeLoss (G.induce {y | y ≠ x}) S T v ≤
        (G.induce {y | y ≠ x}).degree v +
          (if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0)) :
    deletedNeighborhood G x ⊆ S ∪ T := by
  intro v hv
  have hvx := (mem_deletedNeighborhood G x v).mp hv
  exact mem_union_of_one_defect_compensated
    (d := d) (degree := (G.induce {y | y ≠ x}).degree v)
    (loss := crossEdgeLoss (G.induce {y | y ≠ x}) S T v)
    S T hd v (by
      rw [degree_induce_delete_eq, hreg]
      simp [hvx]) (hbudget v)

end Erdos85
