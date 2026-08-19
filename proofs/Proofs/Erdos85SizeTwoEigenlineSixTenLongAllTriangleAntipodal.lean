import Proofs.Erdos85SizeTwoEigenlineSixTenLongAllTfOffsets

/-!
# Antipodal color of the all-triangle C10 diagonal block

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

If the long ambient cycle lies in the all-triangle sector, every one of its
vertices has triangle-free degree zero.  Hence the triangle-free color is
absent from its entire diagonal defect block: there, second-order defect
adjacency is exactly antipodal adjacency.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- On an all-triangle long shore, diagonal second-order defect adjacency is
exactly antipodal adjacency. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_defectAdj_iff_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (b : (G.induce c.supp).ConnectedComponent)
    (hball : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0)
    (x y : c.supp) (hx : x ∈ b.supp) :
    ((secondOrderDefectGraph G).induce c.supp).Adj x y ↔
      (antipodalGraph G).Adj x.1 y.1 := by
  constructor
  · intro hK
    change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x.1 y.1 at hK
    rcases hK with hanti | htf
    · exact hanti
    · have hymem : y.1 ∈ (triangleFreeEdgeGraph G).neighborFinset x.1 :=
        ((triangleFreeEdgeGraph G).mem_neighborFinset x.1 y.1).mpr htf
      have hpos : 0 < (triangleFreeEdgeGraph G).degree x.1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨y.1, hymem⟩
      rw [hball x hx] at hpos
      omega
  · intro hanti
    change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x.1 y.1
    exact Or.inl hanti

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_defectAdj_iff_antipodal
