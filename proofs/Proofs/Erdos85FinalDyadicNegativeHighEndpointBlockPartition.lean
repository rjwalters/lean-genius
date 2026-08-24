import Proofs.Erdos85FinalDyadicNegativeHighEndpointBlockMatching

/-!
# Endpoint block partition of the negative-high defect neighborhood

At saturated support, the defect neighbors in `M` of a point in an empty
block are exactly its unique matched points in all the other empty blocks.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The induced `M`-neighborhood of a point in an empty block is the disjoint
union of its intersections with all other empty blocks. -/
theorem finalDyadic_endpoint_negativeHigh_defectNeighbor_eq_biUnion_blocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {e x : V} (he : e ∈ emptyLineCenters G S)
    (hx : x ∈ G.neighborFinset e) :
    ((emptyLineCenters G S).erase e).biUnion
        (fun f => (secondOrderDefectGraph G).neighborFinset x ∩
          G.neighborFinset f) =
      (secondOrderDefectGraph G).neighborFinset x ∩
        finalDyadicNegativeHighCutCenters G S j r := by
  let D := secondOrderDefectGraph G
  let E := emptyLineCenters G S
  let M := finalDyadicNegativeHighCutCenters G S j r
  have hxM := finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique he hx
  have hclosure := finalDyadic_negativeHigh_endpoint_defectClosure
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique hxM
  change (D.neighborFinset x ∩ M).card = E.card - 1 ∧ _ at hclosure
  have hpair : (↑(E.erase e) : Set V).PairwiseDisjoint
      (fun f => D.neighborFinset x ∩ G.neighborFinset f) := by
    intro f hf g hg hfg
    exact (finalDyadic_emptyCenter_neighborFinset_disjoint
      G hfree S hemptyClique
        (Finset.mem_of_mem_erase hf)
        (Finset.mem_of_mem_erase hg) hfg).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hunionSub : (E.erase e).biUnion
      (fun f => D.neighborFinset x ∩ G.neighborFinset f) ⊆
        D.neighborFinset x ∩ M := by
    intro y hy
    obtain ⟨f, hf, hyBlock⟩ := Finset.mem_biUnion.mp hy
    have hfE : f ∈ E := Finset.mem_of_mem_erase hf
    have hyData := Finset.mem_inter.mp hyBlock
    have hyM := finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hfE hyData.2
    exact Finset.mem_inter.mpr ⟨hyData.1, hyM⟩
  have hunionCard : ((E.erase e).biUnion
      (fun f => D.neighborFinset x ∩ G.neighborFinset f)).card =
        E.card - 1 := by
    rw [Finset.card_biUnion hpair]
    calc
      (∑ f ∈ E.erase e,
          (D.neighborFinset x ∩ G.neighborFinset f).card) =
          ∑ _f ∈ E.erase e, 1 := by
            apply Finset.sum_congr rfl
            intro f hf
            have hfData := Finset.mem_erase.mp hf
            exact finalDyadic_endpoint_otherEmptyBlock_defectNeighbor_card_eq_one
              G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
                hsupport hemptyClique he hfData.2 hfData.1.symm hx
      _ = (E.erase e).card := by simp
      _ = E.card - 1 := Finset.card_erase_of_mem he
  change (E.erase e).biUnion
      (fun f => D.neighborFinset x ∩ G.neighborFinset f) =
        D.neighborFinset x ∩ M
  exact Finset.eq_of_subset_of_card_le hunionSub (by
    rw [hunionCard, hclosure.1])

end


end Erdos85

#print axioms
  Erdos85.finalDyadic_endpoint_negativeHigh_defectNeighbor_eq_biUnion_blocks
