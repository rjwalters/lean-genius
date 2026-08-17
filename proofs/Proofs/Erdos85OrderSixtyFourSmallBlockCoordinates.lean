import Proofs.Erdos85CrossDefectComponentCommonNeighbor
import Proofs.Erdos85OrderSixtyFourSevenComponentLocal

/-! # Coordinatizing order 64 by two small defect blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Any two distinct order-eight defect blocks coordinatize all 64 ambient
vertices: every cell of their `8 × 8` product has a unique common-neighbor
completion, and every ambient vertex has a unique coordinate cell. -/
theorem orderSixtyFour_seven_defect_components_smallBlock_coordinates
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
          ∀ (_hef : e ≠ f),
            (∀ p : e.supp × f.supp, ∃! z : Fin 64,
              G.Adj p.1.1 z ∧ G.Adj p.2.1 z) ∧
            ∀ z : Fin 64, ∃! p : e.supp × f.supp,
              G.Adj p.1.1 z ∧ G.Adj p.2.1 z := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, _htwo, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, heone⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfone⟩ := hsmall f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  constructor
  · intro p
    exact existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hef p.1 p.2
  · intro z
    let E := componentNeighborFinset G D e z
    let F := componentNeighborFinset G D f z
    have hEcard : E.card = 1 := heone z
    have hFcard : F.card = 1 := hfone z
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hEcard
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hFcard
    have hxE : x ∈ E := by rw [hx]; simp
    have hyF : y ∈ F := by rw [hy]; simp
    have hxcomp : x ∈ e.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact (Finset.mem_filter.mp hxE).2
    have hycomp : y ∈ f.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact (Finset.mem_filter.mp hyF).2
    let xs : e.supp := ⟨x, hxcomp⟩
    let ys : f.supp := ⟨y, hycomp⟩
    refine ⟨(xs, ys), ?_, ?_⟩
    · constructor
      · exact ((G.mem_neighborFinset z x).mp
          (Finset.mem_filter.mp hxE).1).symm
      · exact ((G.mem_neighborFinset z y).mp
          (Finset.mem_filter.mp hyF).1).symm
    · intro p hp
      apply Prod.ext
      · apply Subtype.ext
        have hpE : p.1.1 ∈ E := by
          apply Finset.mem_filter.mpr
          refine ⟨(G.mem_neighborFinset z p.1.1).mpr hp.1.symm, ?_⟩
          exact (ConnectedComponent.mem_supp_iff e p.1.1).mp p.1.2
        rw [hx] at hpE
        simpa [xs] using hpE
      · apply Subtype.ext
        have hpF : p.2.1 ∈ F := by
          apply Finset.mem_filter.mpr
          refine ⟨(G.mem_neighborFinset z p.2.1).mpr hp.2.symm, ?_⟩
          exact (ConnectedComponent.mem_supp_iff f p.2.1).mp p.2.2
        rw [hy] at hpF
        simpa [ys] using hpF

end

end Erdos85
