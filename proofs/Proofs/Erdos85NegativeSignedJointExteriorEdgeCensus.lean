import Proofs.Erdos85NegativeSignedJointOutsidePairEncoding

/-! # Exact sign-stratified exterior-edge census -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def negativeSignedJointExteriorEdgeStratum
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : Fin 64 → ℤ) (k : ℤ) : Finset (Sym2 c.supp) :=
  (exteriorPairGraph G c.supp).edgeFinset.filter fun e ↦
    ∑ u ∈ e.toFinset, s u.1 = k

private theorem outsidePair_signSum_eq
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : Fin 64 → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hcard : ∀ x : Fin 64,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (z : {x : Fin 64 // x ∉ c.supp}) :
    ∑ u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset,
        s u.1 = (G.adjMatrix ℤ).mulVec s z.1 := by
  rw [outsidePair_toFinset]
  calc
    (∑ u ∈ componentNeighborSubtypeFinset G
        (secondOrderDefectGraph G) c z.1, s u.1) =
        ∑ y ∈ componentNeighborFinset G
          (secondOrderDefectGraph G) c z.1, s y := by
      apply Finset.sum_bij (fun u _ ↦ u.1)
      · intro u hu; exact Finset.mem_subtype.mp hu
      · intro u _ v _ huv; exact Subtype.ext huv
      · intro y hy
        have hys : y ∈ c.supp :=
          (ConnectedComponent.mem_supp_iff c y).mpr
            (Finset.mem_filter.mp hy).2
        exact ⟨⟨y, hys⟩, Finset.mem_subtype.mpr hy, rfl⟩
      · simp
    _ = ∑ y ∈ G.neighborFinset z.1, s y := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro y hy hyout
      have hyc : y ∉ c.supp := by
        intro hyin
        apply hyout
        exact Finset.mem_filter.mpr ⟨hy,
          (ConnectedComponent.mem_supp_iff c y).mp hyin⟩
      simp [hs_out y hyc]
    _ = (G.adjMatrix ℤ).mulVec s z.1 := by
      rw [SimpleGraph.adjMatrix_mulVec_apply]

theorem orderSixtyFour_negativeSignedJoint_exteriorEdgeCensus
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 16)
    (hconn : (G.induce c.supp).Connected)
    (s : Fin 64 → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z)
    (hmu : mu = -1 ∨ mu = -3 ∨ mu = -5) :
    let PP := negativeSignedJointExteriorEdgeStratum G c s 2
    let PN := negativeSignedJointExteriorEdgeStratum G c s 0
    let NN := negativeSignedJointExteriorEdgeStratum G c s (-2)
    (mu = -1 ∧ PP.card = 8 ∧ PN.card = 32 ∧ NN.card = 8) ∨
    (mu = -3 ∧ PP.card = 12 ∧ PN.card = 24 ∧ NN.card = 12) ∨
    (mu = -5 ∧ PP.card = 16 ∧ PN.card = 16 ∧ NN.card = 16) := by
  classical
  dsimp only
  obtain ⟨_label, hqcard, hcard, hinc, _himage, _hRreg, hRedges,
      _houtreg, _houtfree, _hcross⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility
      G hfree hreg c hc
  let e := outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
    hcard hinc hqcard hRedges
  let OPP := negativeSignedJointPositivePairOwners G c s
  let OPN := negativeSignedJointMixedPairOwners G c s
  let ONN := negativeSignedJointNegativePairOwners G c s
  let EPP := negativeSignedJointExteriorEdgeStratum G c s 2
  let EPN := negativeSignedJointExteriorEdgeStratum G c s 0
  let ENN := negativeSignedJointExteriorEdgeStratum G c s (-2)
  have hsum (z : {x : Fin 64 // x ∉ c.supp}) :
      ∑ u ∈ (e z).1.toFinset, s u.1 = (G.adjMatrix ℤ).mulVec s z.1 := by
    rw [outsidePairEdgeEquiv_apply]
    exact outsidePair_signSum_eq G c s hs_out hcard z
  have card_transport (O : Finset (Fin 64)) (E : Finset (Sym2 c.supp))
      (hout : ∀ x, x ∈ O → x ∉ c.supp)
      (hEsub : E ⊆ (exteriorPairGraph G c.supp).edgeFinset)
      (hpred : ∀ z : {x : Fin 64 // x ∉ c.supp},
        z.1 ∈ O ↔ (e z).1 ∈ E) : O.card = E.card := by
    let OS := (Finset.univ : Finset {x : Fin 64 // x ∉ c.supp}).filter
      fun z ↦ z.1 ∈ O
    have hOS : OS.card = O.card := by
      apply Finset.card_bij (fun z _ ↦ z.1)
      · intro z hz
        exact (Finset.mem_filter.mp hz).2
      · intro z _ w _ h; exact Subtype.ext h
      · intro x hx
        exact ⟨⟨x, hout x hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    have hOSE : OS.card = E.card := by
      apply Finset.card_bij (fun z _ ↦ (e z).1)
      · intro z hz
        exact (hpred z).mp (Finset.mem_filter.mp hz).2
      · intro z _ w _ h
        exact e.injective (Subtype.ext h)
      · intro x hx
        let ex : (exteriorPairGraph G c.supp).edgeFinset := ⟨x,
          hEsub hx⟩
        let z := e.symm ex
        refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · apply (hpred z).mpr
          simpa [ex, z] using hx
        · exact congrArg Subtype.val (e.apply_symm_apply ex)
    exact hOS.symm.trans hOSE
  have hPP : OPP.card = EPP.card := by
    apply card_transport OPP EPP
    · intro x hx
      exact (Finset.mem_filter.mp hx).2.1
    · exact Finset.filter_subset _ _
    · intro z
      simp only [OPP, EPP, negativeSignedJointPositivePairOwners,
        negativeSignedJointExteriorEdgeStratum, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, ha⟩
        exact ⟨(e z).2, (hsum z).trans ha⟩
      · rintro ⟨_, heq⟩
        exact ⟨z.2, (hsum z).symm.trans heq⟩
  have hPN : OPN.card = EPN.card := by
    apply card_transport OPN EPN
    · intro x hx
      exact (Finset.mem_filter.mp hx).2.1
    · exact Finset.filter_subset _ _
    · intro z
      simp only [OPN, EPN, negativeSignedJointMixedPairOwners,
        negativeSignedJointExteriorEdgeStratum, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, ha⟩
        exact ⟨(e z).2, (hsum z).trans ha⟩
      · rintro ⟨_, heq⟩
        exact ⟨z.2, (hsum z).symm.trans heq⟩
  have hNN : ONN.card = ENN.card := by
    apply card_transport ONN ENN
    · intro x hx
      exact (Finset.mem_filter.mp hx).2.1
    · exact Finset.filter_subset _ _
    · intro z
      simp only [ONN, ENN, negativeSignedJointNegativePairOwners,
        negativeSignedJointExteriorEdgeStratum, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, ha⟩
        exact ⟨(e z).2, (hsum z).trans ha⟩
      · rintro ⟨_, heq⟩
        exact ⟨z.2, (hsum z).symm.trans heq⟩
  have howners := orderSixtyFour_negativeSignedJoint_connected_ownerProfile
    G hfree hreg c hc hconn s mu hs_out hs_in hH hD hmu
  change (mu = -1 ∧ OPP.card = 8 ∧ OPN.card = 32 ∧ ONN.card = 8) ∨
    (mu = -3 ∧ OPP.card = 12 ∧ OPN.card = 24 ∧ ONN.card = 12) ∨
    (mu = -5 ∧ OPP.card = 16 ∧ OPN.card = 16 ∧ ONN.card = 16)
      at howners
  rw [hPP, hPN, hNN] at howners
  exact howners

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_negativeSignedJoint_exteriorEdgeCensus
