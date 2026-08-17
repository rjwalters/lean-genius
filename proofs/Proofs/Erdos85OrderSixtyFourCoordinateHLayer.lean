import Proofs.Erdos85OrderSixtyFourSmallBlockCoordinateCharacterization

/-! # The H16 layer in small-block grid coordinates -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In coordinates supplied by two small defect blocks, the distinguished
order-16 component occupies exactly two cells in every row and every column.
Thus its grid support is a two-regular bipartite graph on the row and column
blocks. -/
theorem orderSixtyFour_seven_defect_components_coordinate_HLayer_degrees
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      ∀ e, e ≠ c → e.supp.ncard = 8 ∧
        ∀ f, f ≠ c → f.supp.ncard = 8 ∧
          ∀ (_hef : e ≠ f), ∃ φ : Fin 64 ≃ e.supp × f.supp,
            (∀ x : e.supp,
              ((Finset.univ : Finset (Fin 64)).filter fun z =>
                (secondOrderDefectGraph G).connectedComponentMk z = c ∧
                (φ z).1 = x).card = 2) ∧
            ∀ y : f.supp,
              ((Finset.univ : Finset (Fin 64)).filter fun z =>
                (secondOrderDefectGraph G).connectedComponentMk z = c ∧
                (φ z).2 = y).card = 2 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_smallBlock_coordinate_iff
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecoords⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcoords⟩ := hecoords f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  obtain ⟨φ, hE, hF⟩ := hfcoords hef
  refine ⟨φ, ?_, ?_⟩
  · intro x
    have hcard : (componentNeighborFinset G D c x.1).card = 2 := by
      have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
        G hfree hmin hcover c x.1
      have h' : 8 * (componentNeighborFinset G D c x.1).card = 16 := by
        simpa [D, hc16] using h
      omega
    have heq :
        ((Finset.univ : Finset (Fin 64)).filter fun z =>
          D.connectedComponentMk z = c ∧ (φ z).1 = x) =
        componentNeighborFinset G D c x.1 := by
      ext z
      simp [componentNeighborFinset, D, hE z x, eq_comm, and_comm]
    rw [heq, hcard]
  · intro y
    have hcard : (componentNeighborFinset G D c y.1).card = 2 := by
      have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
        G hfree hmin hcover c y.1
      have h' : 8 * (componentNeighborFinset G D c y.1).card = 16 := by
        simpa [D, hc16] using h
      omega
    have heq :
        ((Finset.univ : Finset (Fin 64)).filter fun z =>
          D.connectedComponentMk z = c ∧ (φ z).2 = y) =
        componentNeighborFinset G D c y.1 := by
      ext z
      simp [componentNeighborFinset, D, hF z y, eq_comm, and_comm]
    rw [heq, hcard]

end

end Erdos85
