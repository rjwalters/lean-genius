import Proofs.Erdos85SizeTwoMuNegOneSelfCellZeroSix
import Proofs.Erdos85SizeTwoMuNegOneSectorSwitchRouting

/-! # Quotient router for the `mu=-1`, `(k,r)=(0,6)` self cell

The graph-level ledger socket is
`Erdos85.orderSixtyFour_sizeTwo_muNegOne_zeroSix_false_of_ledger`, defined in
the imported terminal module. This compatibility module intentionally does
not redeclare that theorem.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Vanishing normalized cycle entries force the all-triangle branch of the
internal-cycle dichotomy, hence triangle-free degree zero on the shore. -/
theorem binarySquare_regular_sizeTwoPart_eight_muNegOne_cycleEntriesZero_forces_allTriangle
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
      {u (z - 1), u (z + 1)})
    (hzero : MuNegOneC8CycleEntriesZero (fun i j ↦
      ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ (u i) (u j))) :
    ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0 := by
  classical
  rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
    G hfree (q := 8) (by omega) (by decide) hreg hcard c hc a with hall0 | hall2
  · exact hall0
  · exfalso
    have hu0a : u 0 ∈ a.supp := by
      rw [← hurange]
      exact ⟨0, rfl⟩
    have hH : (G.induce c.supp).Adj (u 0) (u 1) := by
      rw [← (G.induce c.supp).mem_neighborFinset, hu]
      simp
    have hdeg : (triangleFreeEdgeGraph G).degree (u 0).1 = 2 :=
      hall2 (u 0) hu0a
    have htf : (triangleFreeEdgeGraph G).Adj (u 0).1 (u 1).1 := by
      have hsubset :
          (triangleFreeEdgeGraph G).neighborFinset (u 0).1 ⊆
            Finset.image Subtype.val ((G.induce c.supp).neighborFinset (u 0)) := by
        intro y hy
        have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u 0).1 y := by
          rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
          exact ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mp hy
        have hyc : y ∈ c.supp := by
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff c y]
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hpair.2).symm.trans
              ((SimpleGraph.ConnectedComponent.mem_supp_iff c (u 0).1).mp (u 0).2)
        exact Finset.mem_image.mpr ⟨⟨y, hyc⟩,
          ((G.induce c.supp).mem_neighborFinset _ _).mpr hpair.1, rfl⟩
      have hcardT : ((triangleFreeEdgeGraph G).neighborFinset (u 0).1).card = 2 := by
        simpa using hdeg
      have hcardH : (Finset.image Subtype.val
          ((G.induce c.supp).neighborFinset (u 0))).card = 2 := by
        rw [Finset.card_image_of_injective _ Subtype.val_injective,
          (G.induce c.supp).card_neighborFinset_eq_degree]
        exact binarySquare_regular_degree_induce_defectComponent_eq_part
          G hfree (by omega) hreg hcard c (m := 2) hc (u 0)
      have heq := Finset.Subset.antisymm hsubset
        (Finset.eq_of_subset_of_card_le hsubset (by omega) |>.symm.subset)
      have hu1 : (u 1).1 ∈ Finset.image Subtype.val
          ((G.induce c.supp).neighborFinset (u 0)) :=
        Finset.mem_image.mpr ⟨u 1,
          ((G.induce c.supp).mem_neighborFinset _ _).mpr hH, rfl⟩
      exact ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mp (by
        rw [heq]
        exact hu1)
    have hK : ((secondOrderDefectGraph G).induce c.supp).Adj (u 0) (u 1) := by
      rw [triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree] at htf
      exact htf.2
    exact hzero.2 (by simpa [SimpleGraph.adjMatrix_apply] using hK)

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_muNegOne_cycleEntriesZero_forces_allTriangle
