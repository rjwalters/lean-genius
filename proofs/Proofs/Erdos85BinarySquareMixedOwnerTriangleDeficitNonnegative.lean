import Proofs.Erdos85BinarySquareOwnerTriangleInjection
import Proofs.Erdos85BinarySquareMixedOwnerTriangleDeficit

/-!
# Nonnegativity of the mixed-owner triangle deficit

The previously signed deficit is a genuine nonnegative count: unique edge
ownership injects every monochromatic owner triangle into a complement
triangle.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquareMixedOwnerTriangleDeficit_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcard : 3 ≤ Fintype.card V) :
    0 ≤ binarySquareMixedOwnerTriangleDeficit G := by
  have hle := sum_componentOwner_triangleMinorCount_le_defectComplement
    G hfree hcard
  unfold binarySquareMixedOwnerTriangleDeficit
  rw [sub_nonneg]
  exact_mod_cast hle

end


end Erdos85

#print axioms Erdos85.binarySquareMixedOwnerTriangleDeficit_nonneg
