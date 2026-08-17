import Proofs.Erdos85HoffmanRatioBound

/-!
# Equality partitions for square-order owner graphs

The order-`q` defect components that attain the sharp owner-graph Hoffman
bound are not only maximum cocliques: every vertex outside such a component
has exactly `m_c` neighbors in it in owner color `c`.  This is the equitable
partition law needed to make simultaneous Hoffman equality usable.
-/

open SimpleGraph

namespace Erdos85

/-- **Pointwise Hoffman-equality partition law.**  Let `e` be a defect
component of order `q`, and let owner color `c` have normalized size `m_c`.
Every vertex outside `e` has exactly `m_c` owner-`c` neighbors in `e`.

The proof exposes that this equality structure was already latent in the
pointwise cross-component owner-coordinate count; no spectral equality-case
argument is needed. -/
theorem binarySquare_regular_sizeQ_component_ownerNeighborCard_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (he : e.supp.ncard = q) (hc : c.supp.ncard = q * m_c)
    (x : V) (hx : (secondOrderDefectGraph G).connectedComponentMk x ≠ e) :
    (((componentOwnerGraph G (secondOrderDefectGraph G) c).neighborFinset x) ∩
        e.supp.toFinite.toFinset).card = m_c := by
  let D := secondOrderDefectGraph G
  let f := D.connectedComponentMk x
  have hxf : x ∈ f.supp := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff f x).mpr rfl
  have hfe : f ≠ e := by simpa [f, D] using hx
  have hcount := binarySquare_regular_crossComponent_ownerCoordinate_card
    G hfree hq hreg hcard f e c hfe (m_f := 1) hc
      (by simpa using he) ⟨x, hxf⟩
  have hfin :
      ((e.supp.toFinite.toFinset).filter fun y =>
        (componentNeighborFinset G D c x ∩
          componentNeighborFinset G D c y).Nonempty) =
        (componentOwnerGraph G D c).neighborFinset x ∩
          e.supp.toFinite.toFinset := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hye, hcommon⟩
      have hye' : D.connectedComponentMk y = e :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff e y).mp (by simpa using hye)
      have hxy : x ≠ y := by
        intro hxy
        subst y
        exact hx (by simpa [D] using hye')
      exact ⟨(componentOwnerGraph_adj G D c x y).mpr ⟨hxy, hcommon⟩, hye⟩
    · rintro ⟨howner, hye⟩
      exact ⟨hye, ((componentOwnerGraph_adj G D c x y).mp howner).2⟩
  rw [hfin] at hcount
  simpa using hcount

end Erdos85
