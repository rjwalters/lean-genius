import Proofs.Erdos85SizeTwoEigenlineSixTenLongAllTriangleShape

/-!
# Excluding the low all-triangle C10 support

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A C10 distance-two pair has its intervening cycle vertex as a common
ambient neighbor, so it cannot simultaneously be a second-order defect
pair.  This excludes the `{±2,±3}` all-triangle support branch. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_not_long_support_two_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hoff : ∀ i j,
      ((secondOrderDefectGraph G).induce c.supp).Adj (v i) (v j) ↔
        j - i = 2 ∨ j - i = 3 ∨ j - i = 7 ∨ j - i = 8) :
    False := by
  have hDsub : ((secondOrderDefectGraph G).induce c.supp).Adj (v 0) (v 2) :=
    (hoff 0 2).2 (Or.inl (by norm_num))
  have hD : (secondOrderDefectGraph G).Adj (v 0).1 (v 2).1 := hDsub
  have h01sub : (G.induce c.supp).Adj (v 0) (v 1) := by
    rw [← (G.induce c.supp).mem_neighborFinset, hv]
    norm_num
  have h21sub : (G.induce c.supp).Adj (v 2) (v 1) := by
    rw [← (G.induce c.supp).mem_neighborFinset, hv]
    norm_num
  have h02 : (v 0).1 ≠ (v 2).1 := by
    intro h
    have : (0 : ZMod 10) = 2 := hvinj (Subtype.ext h)
    exact (by decide : (0 : ZMod 10) ≠ 2) this
  exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree h02
    h01sub h21sub) hD

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_not_long_support_two_three
