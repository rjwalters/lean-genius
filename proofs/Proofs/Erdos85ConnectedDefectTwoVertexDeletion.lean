import Proofs.Erdos85TwoSeparatorConnectivityBridge
import Proofs.Erdos85TwoSeparatorMantelContradiction

/-!
# Two-vertex-deletion connectivity of the connected defect graph

The explicit two-separator contradiction and the canonical shore extraction
combine to show that deleting any two defect vertices leaves a connected
induced graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the even binary-square connected branch (`q ≥ 8`), every two-vertex
deletion of the second-order defect graph remains connected. -/
theorem binarySquare_connected_secondOrderDefect_delete_two_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q r : ℕ}
    (hq8 : 8 ≤ q) (hr : 2 ≤ r) (hq : q = 2 * (r + 1))
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Connected) :
    ∀ W : Finset V, W.card = 2 →
      ((secondOrderDefectGraph G).induce
        (↑(Finset.univ \ W) : Set V)).Connected := by
  let D := secondOrderDefectGraph G
  apply induce_sdiff_connected_of_no_twoSeparator_partition D
  · rw [hcard]
    nlinarith
  · intro S T W hSne hTne hcover hST hSW hTW hno hWcard hcards
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hWcard
    have hxS : x ∉ S := by
      intro hx
      exact Finset.disjoint_left.mp hSW hx (by simp)
    have hyS : y ∉ S := by
      intro hy
      exact Finset.disjoint_left.mp hSW hy (by simp)
    have hxT : x ∉ T := by
      intro hx
      exact Finset.disjoint_left.mp hTW hx (by simp)
    have hyT : y ∉ T := by
      intro hy
      exact Finset.disjoint_left.mp hTW hy (by simp)
    apply false_of_binarySquare_connected_twoSeparator_partition
      G hfree hq8 hr hq hreg hcard hconn S T x y hxy
        hcover hST hxS hyS hxT hyT
    · simpa [D] using hno
    · exact hSne
    · exact hTne
    · simpa [hcard] using hcards

end

end Erdos85

#print axioms Erdos85.binarySquare_connected_secondOrderDefect_delete_two_connected
