import Proofs.Erdos85BinarySquareRoutingRowDensityResidualStars

/-! # Cross-root compatibility of routing centers -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Distinct roots in one defect component share at most one center of any
fixed owner color.  Two shared centers would form a four-cycle with the two
roots.  This is the basic cross-root compatibility law for the canonical
routing-row star decompositions. -/
theorem componentCrossNeighborFinset_inter_card_le_one_of_distinct_roots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source owner : (secondOrderDefectGraph G).ConnectedComponent}
    (x x' : source.supp) (hxx' : x ≠ x') :
    (componentCrossNeighborFinset G owner x ∩
      componentCrossNeighborFinset G owner x').card ≤ 1 := by
  classical
  by_contra hle
  have hlt : 1 < (componentCrossNeighborFinset G owner x ∩
      componentCrossNeighborFinset G owner x').card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hlt
  have huData := Finset.mem_inter.mp hu
  have hvData := Finset.mem_inter.mp hv
  have hxu : G.Adj x.1 u.1 := (Finset.mem_filter.mp huData.1).2
  have hx'u : G.Adj x'.1 u.1 := (Finset.mem_filter.mp huData.2).2
  have hxv : G.Adj x.1 v.1 := (Finset.mem_filter.mp hvData.1).2
  have hx'v : G.Adj x'.1 v.1 := (Finset.mem_filter.mp hvData.2).2
  have hxxVal : x.1 ≠ x'.1 := by
    intro heq
    exact hxx' (Subtype.ext heq)
  have huvVal : u.1 ≠ v.1 := by
    intro heq
    exact huv (Subtype.ext heq)
  exact hfree (containsC4_of_two_common hxxVal huvVal
    hxu.symm hx'u.symm hxv.symm hx'v.symm)

end

end Erdos85

#print axioms Erdos85.componentCrossNeighborFinset_inter_card_le_one_of_distinct_roots
