import Proofs.Erdos85CrossEdgeTriangleDichotomy
import Proofs.Erdos85OrderSixtyFourOutsideEdgeBijection

/-! # The label-free hit law for a size-two defect block

When every vertex outside a defect component selects exactly two vertices of
the component, `outsidePair` records that selection without choosing labels.
The general row-hit law then says that an internal vertex has a common
neighbour with the outside owner on the outside precisely when it is adjacent
to neither endpoint of the selected pair.  This is the graph-facing interface
needed by the eigenline-free unordered-pair model.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Label-free size-two row-hit law.  The exterior common neighbour exists
uniquely exactly when neither endpoint of the outside owner's selected pair is
adjacent to the internal vertex. -/
theorem existsUnique_exterior_common_iff_outsidePair_forall_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (u : {x : V // x ∉ c.supp}) (x : c.supp) :
    (∃! y, G.Adj u.1 y ∧ y ∉ c.supp ∧ G.Adj x.1 y) ↔
      ∀ z, z ∈ (outsidePair G (secondOrderDefectGraph G) c hcard u).toFinset →
        ¬ G.Adj x.1 z.1 := by
  have hrow := exists_exterior_common_iff_no_internal_common
    G hfree c x.2 u.2
  constructor
  · rintro ⟨y, hy, hyuniq⟩ z hz hxz
    have hex : ∃ y, G.Adj u.1 y ∧ y ∉ c.supp ∧ G.Adj x.1 y :=
      ⟨y, hy⟩
    have hno := hrow.1.mp hex
    apply hno
    refine ⟨z.1, hxz, z.2, ?_⟩
    exact ((mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard u z).mp hz).symm
  · intro hpairs
    have hno : ¬ ∃ y, G.Adj x.1 y ∧ y ∈ c.supp ∧ G.Adj u.1 y := by
      rintro ⟨y, hxy, hyc, huy⟩
      let z : c.supp := ⟨y, hyc⟩
      have hz : z ∈
          (outsidePair G (secondOrderDefectGraph G) c hcard u).toFinset :=
        (mem_outsidePair_toFinset_iff_adj
          G (secondOrderDefectGraph G) c hcard u z).mpr huy.symm
      exact hpairs z hz hxy
    have hex := hrow.1.mpr hno
    exact hrow.2 hex

#print axioms Erdos85.existsUnique_exterior_common_iff_outsidePair_forall_not_adj

end

end Erdos85
