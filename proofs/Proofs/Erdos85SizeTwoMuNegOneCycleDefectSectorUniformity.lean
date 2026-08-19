import Proofs.Erdos85SizeTwoMuNegOneEightEightSectorParameterGrid

/-!
# All-row cycle-defect sector uniformity on a normalized C8 shore

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The discrete aligned ledger tags a shore using the two cycle entries in row
zero.  Owner-grid models need the corresponding statement in every cyclic
row.  The internal-cycle sector dichotomy is stronger than the row-zero tag:
triangle-free degree is uniformly zero or uniformly two throughout the
ambient C8.  Since the induced ambient degree is two, the latter case says
both cyclic neighbors are defect neighbors in every row.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- On a normalized C8 shore of a size-two component, the two ambient cycle
edges are either absent from the defect graph in every row or present in the
defect graph in every row. -/
theorem binarySquare_regular_sizeTwoPart_eight_cycleDefect_allZero_or_allOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    (∀ i, ¬ K.Adj (u i) (u (i - 1)) ∧
      ¬ K.Adj (u i) (u (i + 1))) ∨
    (∀ i, K.Adj (u i) (u (i - 1)) ∧
      K.Adj (u i) (u (i + 1))) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hmem (i : ZMod 8) : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hsector := binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
    G hfree (q := 8) (by omega) (by decide) hreg hcard c hc a
  rcases hsector with hall0 | hall2
  · left
    intro i
    constructor
    · intro hK
      have hH : H.Adj (u i) (u (i - 1)) := by
        rw [← H.mem_neighborFinset, hu]
        simp
      have htf : (triangleFreeEdgeGraph G).Adj (u i).1 (u (i - 1)).1 := by
        rw [triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact ⟨hH, hK⟩
      have hpos : 0 < (triangleFreeEdgeGraph G).degree (u i).1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨(u (i - 1)).1,
          ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf⟩
      rw [hall0 (u i) (hmem i)] at hpos
      omega
    · intro hK
      have hH : H.Adj (u i) (u (i + 1)) := by
        rw [← H.mem_neighborFinset, hu]
        simp
      have htf : (triangleFreeEdgeGraph G).Adj (u i).1 (u (i + 1)).1 := by
        rw [triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact ⟨hH, hK⟩
      have hpos : 0 < (triangleFreeEdgeGraph G).degree (u i).1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨(u (i + 1)).1,
          ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf⟩
      rw [hall0 (u i) (hmem i)] at hpos
      omega
  · right
    intro i
    let T := (Finset.univ : Finset c.supp).filter fun y ↦
      (triangleFreeEdgeGraph G).Adj (u i).1 y.1
    have himage : Finset.image Subtype.val T =
        (triangleFreeEdgeGraph G).neighborFinset (u i).1 := by
      ext y
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro htf
        have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u i).1 y := by
          rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
          exact htf
        have hyc : y ∈ c.supp := by
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff c y]
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hpair.2).symm.trans
              ((SimpleGraph.ConnectedComponent.mem_supp_iff c (u i).1).mp
                (u i).2)
        exact ⟨⟨y, hyc⟩, htf, rfl⟩
    have hTcard : T.card = 2 := by
      rw [← Finset.card_image_of_injective T Subtype.val_injective,
        himage, (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
      exact hall2 (u i) (hmem i)
    have hHdegree : H.degree (u i) = 2 :=
      binarySquare_regular_degree_induce_defectComponent_eq_part
        G hfree (by omega) hreg hcard c (m := 2)
          (by simpa [Nat.mul_comm] using hc) (u i)
    have hTsub : T ⊆ H.neighborFinset (u i) := by
      intro y hy
      have htf := (Finset.mem_filter.mp hy).2
      have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u i).1 y.1 := by
        rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact htf
      exact (H.mem_neighborFinset (u i) y).mpr hpair.1
    have hTeq : T = H.neighborFinset (u i) := by
      apply Finset.eq_of_subset_of_card_le hTsub
      rw [hTcard, H.card_neighborFinset_eq_degree, hHdegree]
    have defect_of_cycle (j : ZMod 8)
        (hj : j = i - 1 ∨ j = i + 1) : K.Adj (u i) (u j) := by
      have hHj : H.Adj (u i) (u j) := by
        rw [← H.mem_neighborFinset, hu]
        rcases hj with rfl | rfl <;> simp
      have hujT : u j ∈ T := by
        rw [hTeq]
        exact (H.mem_neighborFinset (u i) (u j)).mpr hHj
      have htf := (Finset.mem_filter.mp hujT).2
      have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u i).1 (u j).1 := by
        rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact htf
      exact hpair.2
    exact ⟨defect_of_cycle (i - 1) (Or.inl rfl),
      defect_of_cycle (i + 1) (Or.inr rfl)⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_cycleDefect_allZero_or_allOne
