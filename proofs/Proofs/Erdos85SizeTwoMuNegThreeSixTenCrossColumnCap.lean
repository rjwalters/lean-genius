import Proofs.Erdos85SizeTwoMuNegThreeSixTenCrossColumnCensus

/-! # Pointwise long-column bounds in the `mu=-3` six-plus-ten stratum -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
/-- Every long-side cross-defect column has at most two same-sign entries and
therefore at least one opposite-sign entry. Its total column degree is three. -/
theorem orderSixtyFour_sizeTwo_muNegThree_sixTen_crossColumn_cap
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
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    ∀ y : c.supp, y ∈ b.supp →
      let C := componentNeighborFinset K H a y
      let Csame := C.filter fun x ↦ s x.1 = s y.1
      let Copp := C.filter fun x ↦ s x.1 = -s y.1
      C.card = 3 ∧ Csame.card ≤ 2 ∧ 1 ≤ Copp.card := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := G.induce c.supp
  let K := D.induce c.supp
  have hprofile := orderSixtyFour_sizeTwo_muNegThree_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hcensus := orderSixtyFour_sizeTwo_muNegThree_sixTen_crossDefect_census
    G hfree hreg hcard c hc s hs_out hs_in hH hD a b ha hb
  intro y hy
  let C := componentNeighborFinset K H a y
  let Csame := C.filter fun x ↦ s x.1 = s y.1
  let Copp := C.filter fun x ↦ s x.1 = -s y.1
  have hCcard : C.card = 3 := hcensus.2.2 y hy
  have himage (t : ℤ) : Finset.image Subtype.val
      ((K.neighborFinset y).filter fun x ↦ s x.1 = t) =
      (D.neighborFinset y.1).filter fun x ↦ s x = t := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨z, ⟨hK, hsz⟩, rfl⟩
      exact ⟨hK, hsz⟩
    · rintro ⟨hDx, hsx⟩
      have hxc : x ∈ c.supp := by
        rw [ConnectedComponent.mem_supp_iff c x]
        exact (ConnectedComponent.connectedComponentMk_eq_of_adj hDx).symm.trans
          ((ConnectedComponent.mem_supp_iff c y.1).mp y.2)
      exact ⟨⟨x, hxc⟩, ⟨hDx, hsx⟩, rfl⟩
  have hKsame :
      ((K.neighborFinset y).filter fun x ↦ s x.1 = s y.1).card = 2 := by
    rcases hs_in y.1 y.2 with hsy | hsy
    · have hp := (hprofile.2.2 y.1 y.2).2 hsy
      calc
        _ = ((D.neighborFinset y.1).filter fun x ↦ s x = -1).card := by
          rw [← congrArg Finset.card (himage (-1)),
            Finset.card_image_of_injective _ Subtype.val_injective]
          simp [hsy]
        _ = 2 := hp.2.2.1
    · have hp := (hprofile.2.2 y.1 y.2).1 hsy
      calc
        _ = ((D.neighborFinset y.1).filter fun x ↦ s x = 1).card := by
          rw [← congrArg Finset.card (himage 1),
            Finset.card_image_of_injective _ Subtype.val_injective]
          simp [hsy]
        _ = 2 := hp.2.2.1
  have hCsub : C ⊆ K.neighborFinset y := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hsameSub : Csame ⊆
      (K.neighborFinset y).filter fun x ↦ s x.1 = s y.1 := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hCsub hx'.1, hx'.2⟩
  have hsameLe : Csame.card ≤ 2 := by
    rw [← hKsame]
    exact Finset.card_le_card hsameSub
  have hcover : Csame ∪ Copp = C := by
    ext x
    simp only [Csame, Copp, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    · intro hx
      rcases hs_in x.1 x.2 with hsx | hsx <;>
        rcases hs_in y.1 y.2 with hsy | hsy <;> simp_all
  have hdisj : Disjoint Csame Copp := by
    rw [Finset.disjoint_left]
    intro x hxs hxo
    have hs := (Finset.mem_filter.mp hxs).2
    have ho := (Finset.mem_filter.mp hxo).2
    rcases hs_in y.1 y.2 with hsy | hsy <;> omega
  have hsum : Csame.card + Copp.card = 3 := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, hCcard]
  refine ⟨hCcard, hsameLe, ?_⟩
  by_contra hn
  have hoppZero : Copp.card = 0 := Nat.eq_zero_of_not_pos hn
  omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_sixTen_crossColumn_cap
