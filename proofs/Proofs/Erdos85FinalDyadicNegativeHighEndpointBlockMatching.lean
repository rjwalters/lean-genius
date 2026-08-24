import Proofs.Erdos85FinalDyadicNegativeHighEndpointClosure

/-!
# Exact cross-block matching at saturated exceptional support

At the endpoint `c=q`, every negative-high point has exactly one defect
neighbor in each other empty-center block.  Thus any two distinct empty
blocks are joined by a perfect matching in the second-order defect graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At saturated support, a point of one empty-center block has exactly one
second-order-defect neighbor in every other empty-center block. -/
theorem finalDyadic_endpoint_otherEmptyBlock_defectNeighbor_card_eq_one
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
    {e f x : V} (he : e ∈ emptyLineCenters G S)
    (hf : f ∈ emptyLineCenters G S) (hef : e ≠ f)
    (hx : x ∈ G.neighborFinset e) :
    ((secondOrderDefectGraph G).neighborFinset x ∩
      G.neighborFinset f).card = 1 := by
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
  have htargetNonempty : (D.neighborFinset x ∩ G.neighborFinset f).Nonempty := by
    obtain ⟨y, hyf, hyD⟩ :=
      exists_secondOrderDefect_neighbor_in_other_neighborBlock
        G hfree hreg (hemptyClique he hf hef) hx
    exact ⟨y, Finset.mem_inter.mpr ⟨hyD, hyf⟩⟩
  have htargetPos : 1 ≤ (D.neighborFinset x ∩ G.neighborFinset f).card :=
    Finset.one_le_card.mpr htargetNonempty
  have hfe : f ∈ E.erase e := Finset.mem_erase.mpr ⟨hef.symm, hf⟩
  have hnonempty : ∀ g ∈ E.erase e,
      (D.neighborFinset x ∩ G.neighborFinset g).Nonempty := by
    intro g hg
    have hgData := Finset.mem_erase.mp hg
    obtain ⟨y, hyg, hyD⟩ :=
      exists_secondOrderDefect_neighbor_in_other_neighborBlock
        G hfree hreg (hemptyClique he hgData.2 hgData.1.symm) hx
    exact ⟨y, Finset.mem_inter.mpr ⟨hyD, hyg⟩⟩
  have hpair : (↑(E.erase e) : Set V).PairwiseDisjoint
      (fun g => D.neighborFinset x ∩ G.neighborFinset g) := by
    intro g hg k hk hgk
    exact (finalDyadic_emptyCenter_neighborFinset_disjoint
      G hfree S hemptyClique
        (Finset.mem_of_mem_erase hg)
        (Finset.mem_of_mem_erase hk) hgk).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hunionSub : (E.erase e).biUnion
      (fun g => D.neighborFinset x ∩ G.neighborFinset g) ⊆
        D.neighborFinset x ∩ M := by
    intro y hy
    obtain ⟨g, hg, hyBlock⟩ := Finset.mem_biUnion.mp hy
    have hgE : g ∈ E := Finset.mem_of_mem_erase hg
    have hyData := Finset.mem_inter.mp hyBlock
    have hyM := finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hgE hyData.2
    exact Finset.mem_inter.mpr ⟨hyData.1, hyM⟩
  have hsumUpper : (∑ g ∈ E.erase e,
      (D.neighborFinset x ∩ G.neighborFinset g).card) ≤ E.card - 1 := by
    rw [← Finset.card_biUnion hpair]
    exact (Finset.card_le_card hunionSub).trans_eq hclosure.1
  have hrestLower : ((E.erase e).erase f).card ≤
      ∑ g ∈ (E.erase e).erase f,
        (D.neighborFinset x ∩ G.neighborFinset g).card := by
    calc
      _ = ∑ _g ∈ (E.erase e).erase f, 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro g hg
        exact Finset.one_le_card.mpr
          (hnonempty g (Finset.mem_of_mem_erase hg))
  have htotalSplit :
      (∑ g ∈ E.erase e,
        (D.neighborFinset x ∩ G.neighborFinset g).card) =
      (D.neighborFinset x ∩ G.neighborFinset f).card +
        ∑ g ∈ (E.erase e).erase f,
          (D.neighborFinset x ∩ G.neighborFinset g).card := by
    rw [← Finset.sum_erase_add _ _ hfe]
    omega
  have hEpos : 0 < E.card := Finset.card_pos.mpr ⟨e, he⟩
  have heraseCard : (E.erase e).card = E.card - 1 :=
    Finset.card_erase_of_mem he
  have hErasePos : 0 < (E.erase e).card :=
    Finset.card_pos.mpr ⟨f, hfe⟩
  have hEgeTwo : 2 ≤ E.card := by omega
  have hrestCard : ((E.erase e).erase f).card = E.card - 2 := by
    rw [Finset.card_erase_of_mem hfe, heraseCard]
    omega
  rw [htotalSplit] at hsumUpper
  rw [hrestCard] at hrestLower
  change (D.neighborFinset x ∩ G.neighborFinset f).card = 1
  omega

end

end Erdos85

#print axioms
  Erdos85.finalDyadic_endpoint_otherEmptyBlock_defectNeighbor_card_eq_one
