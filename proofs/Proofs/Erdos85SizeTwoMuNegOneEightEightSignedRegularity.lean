import Proofs.Erdos85SizeTwoMuNegThreeEightEightSignedRegularity
import Proofs.Erdos85SizeTwoMuNegOneEightEightReduction

/-! # Signed regularity of the `mu=-1` eight-plus-eight blocks -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
/-- On each of the two ambient eight-cycles, the same-sign degree of the
internal defect block is constant. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_internalSame_regular
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
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    let Ka := K.induce a.supp
    let Kb := K.induce b.supp
    (∀ x y : a.supp,
      ((Ka.neighborFinset x).filter fun z ↦ s z.1.1 = s x.1.1).card =
      ((Ka.neighborFinset y).filter fun z ↦ s z.1.1 = s y.1.1).card) ∧
    (∀ x y : b.supp,
      ((Kb.neighborFinset x).filter fun z ↦ s z.1.1 = s x.1.1).card =
      ((Kb.neighborFinset y).filter fun z ↦ s z.1.1 = s y.1.1).card) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  obtain ⟨ha8, hb8, r, hr2, hr7, haa, habq, hbaq, hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    exact (adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c).symm
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have component_data (d : H.ConnectedComponent)
      (hdiag : componentQuotientMatrix K H d d = 7 - r) :
      let Hd := H.induce d.supp
      let Kd := K.induce d.supp
      (∀ x : d.supp, Hd.degree x = 2) ∧
      (∀ x : d.supp, Kd.degree x = 7 - r) ∧
      (∀ x : d.supp, ∑ y ∈ Hd.neighborFinset x, s y.1.1 = -2 * s x.1.1) := by
    dsimp only
    constructor
    · intro x
      rw [degree_induce_connectedComponent_supp]
      exact hHdegree x.1
    constructor
    · intro x
      rw [← (K.induce d.supp).card_neighborFinset_eq_degree]
      let I := componentNeighborFinset K H d x.1
      have hIcard : I.card = 7 - r := by
        rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal d d x.2]
        exact hdiag
      have heq : ((K.induce d.supp).neighborFinset x).image (fun z ↦ z.1) = I := by
        ext z
        simp [I, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
          H, eq_comm]
      rw [← hIcard, ← heq, Finset.card_image_of_injective]
      exact Subtype.val_injective
    · intro x
      calc
        ∑ y ∈ (H.induce d.supp).neighborFinset x, s y.1.1 =
            ∑ _y ∈ (H.induce d.supp).neighborFinset x, -s x.1.1 := by
          apply Finset.sum_congr rfl
          intro y hy
          have hxy : H.Adj x.1 y.1 :=
            ((H.induce d.supp).mem_neighborFinset x y).mp hy
          have hymem : y.1.1 ∈ componentNeighborFinset G
              (secondOrderDefectGraph G) c x.1.1 := by
            rw [componentNeighborFinset, Finset.mem_filter]
            exact ⟨(G.mem_neighborFinset _ _).mpr hxy, y.1.2⟩
          exact internal_alternation G hfree (by omega) hreg hcard c hc s
            hs_in hs_out hAfull x.1.2 |>.2 y.1.1 hymem
        _ = -2 * s x.1.1 := by
          rw [Finset.sum_const, nsmul_eq_mul,
            (H.induce d.supp).card_neighborFinset_eq_degree,
            degree_induce_connectedComponent_supp, hHdegree]
          ring
  have hda := component_data a haa
  have hdb := component_data b hbb
  constructor
  · exact commuting_component_sameSign_degree_constant H K a
      (fun z : c.supp ↦ s z.1) 2 (7 - r)
      (fun x ↦ hs_in x.1.1 x.1.2) hda.1 hda.2.2 hda.2.1 hcomm
  · exact commuting_component_sameSign_degree_constant H K b
      (fun z : c.supp ↦ s z.1) 2 (7 - r)
      (fun x ↦ hs_in x.1.1 x.1.2) hdb.1 hdb.2.2 hdb.2.1 hcomm

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_internalSame_regular
