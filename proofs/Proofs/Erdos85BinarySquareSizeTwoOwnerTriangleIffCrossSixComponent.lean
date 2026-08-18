import Proofs.Erdos85BinarySquareSizeTwoCrossCycleHexagonComponent
import Proofs.Erdos85BinarySquareSizeTwoCrossComponentSixOwnerTriangle

/-! # Owner triangles are exactly cross components of order six -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For two normalized size-two defect components, the restricted owner
factor contains a triangle exactly when their cross graph has a connected
component of order six. -/
theorem binarySquare_regular_twoSizeTwoParts_ownerTriangle_iff_exists_crossComponent_order_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2) :
    (∃ x y z : source.supp,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      (restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).Adj y z ∧
      (restrictedComponentOwnerGraph G source target).Adj z x) ↔
    ∃ e : (componentCrossBipartiteGraph G source target).ConnectedComponent,
      e.supp.ncard = 6 := by
  constructor
  · rintro ⟨x, y, z, hxy, hyz, hzx, hxyAdj, hyzAdj, hzxAdj⟩
    exact
      binarySquare_regular_twoSizeTwoParts_ownerTriangle_exists_crossComponent_order_six
        G hfree hq hreg hcard source target hsource htarget x y z
          hxy hyz hzx ⟨hxyAdj, hyzAdj, hzxAdj⟩
  · rintro ⟨e, he⟩
    obtain ⟨x, y, z, hxy, hyz, hzx, hxyAdj, hyzAdj, hzxAdj, _⟩ :=
      binarySquare_regular_twoSizeTwoParts_crossComponent_order_six_exists_ownerTriangle
        G hfree hq hreg hcard source target hsource htarget e he
    exact ⟨x, y, z, hxy, hyz, hzx, hxyAdj, hyzAdj, hzxAdj⟩

end

end Erdos85
