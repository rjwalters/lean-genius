import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Shore partition of a non-preconnected finite graph

Reachability from one endpoint of a nonreachable pair gives the canonical
two-shore partition, with no edge crossing between the shores.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A finite non-preconnected graph splits into two nonempty anticomplete
finsets covering its vertex set. -/
theorem exists_nonempty_anticomplete_partition_of_not_preconnected
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hnot : ¬ H.Preconnected) :
    ∃ S T : Finset V,
      S.Nonempty ∧ T.Nonempty ∧ S ∪ T = Finset.univ ∧ Disjoint S T ∧
        ∀ s ∈ S, ∀ t ∈ T, ¬ H.Adj s t := by
  rw [SimpleGraph.Preconnected] at hnot
  push_neg at hnot
  obtain ⟨u, v, huv⟩ := hnot
  let S : Finset V := Finset.univ.filter fun z => H.Reachable u z
  let T : Finset V := Finset.univ \ S
  have huS : u ∈ S := by simp [S, SimpleGraph.Reachable.refl]
  have hvT : v ∈ T := by simp [T, S, huv]
  refine ⟨S, T, ⟨u, huS⟩, ⟨v, hvT⟩, ?_, ?_, ?_⟩
  · simp [T]
  · rw [Finset.disjoint_left]
    intro z hzS hzT
    exact (Finset.mem_sdiff.mp hzT).2 hzS
  · intro s hs t ht hst
    have hus : H.Reachable u s := (Finset.mem_filter.mp hs).2
    have hstReach : H.Reachable s t := H.adj_le_reachable s t hst
    have hut : H.Reachable u t := hus.trans hstReach
    exact (Finset.mem_sdiff.mp ht).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hut⟩)

end

end Erdos85

#print axioms Erdos85.exists_nonempty_anticomplete_partition_of_not_preconnected
