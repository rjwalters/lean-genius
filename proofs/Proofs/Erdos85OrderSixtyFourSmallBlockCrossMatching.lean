import Proofs.Erdos85OrderSixtyFourSevenComponentLocal

/-! # Perfect matchings between the six small defect blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the seven-component order-64 branch, every vertex of any order-eight
defect block has a unique ambient neighbor in every order-eight defect block.
Thus every ordered pair of the six small blocks is joined by a perfect
matching (including the internal matching when the two blocks coincide). -/
theorem orderSixtyFour_seven_defect_components_smallBlocks_unique_neighbor
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
          ∀ x : e.supp, ∃! y : f.supp, G.Adj x.1 y.1 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, _htwo, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, _heone⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfone⟩ := hsmall f hfc
  refine ⟨hf8, ?_⟩
  intro x
  let S := componentNeighborFinset G D f x.1
  have hScard : S.card = 1 := hfone x.1
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hScard
  have hyS : y ∈ S := by rw [hy]; simp
  have hycomp : y ∈ f.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (Finset.mem_filter.mp hyS).2
  let ys : f.supp := ⟨y, hycomp⟩
  refine ⟨ys, ?_, ?_⟩
  · exact (G.mem_neighborFinset x.1 y).mp (Finset.mem_filter.mp hyS).1
  · intro z hxz
    apply Subtype.ext
    have hzS : z.1 ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨(G.mem_neighborFinset x.1 z.1).mpr hxz, ?_⟩
      exact (ConnectedComponent.mem_supp_iff f z.1).mp z.2
    rw [hy] at hzS
    simpa [ys] using hzS

end

end Erdos85
