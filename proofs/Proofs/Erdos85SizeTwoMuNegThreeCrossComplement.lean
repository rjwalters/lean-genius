import Proofs.Erdos85SizeTwoMuNegThreeSameSignCycles
import Proofs.Erdos85ThreeBiregularDecomposition

/-! # The cross nondefect cubic relation at `mu = -3` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Across the two eight-vertex sign shores, defect adjacency is
five-regular, so its bipartite complement is exactly three-regular. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_threeRegular
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
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegThreePositiveShore D c s
    let Xm := MuNegThreeNegativeShore D c s
    (∀ x : Xp,
      ((Finset.univ : Finset Xm).filter fun y ↦ ¬ D.Adj x.1 y.1).card = 3) ∧
    ∀ y : Xm,
      ((Finset.univ : Finset Xp).filter fun x ↦ ¬ D.Adj x.1 y.1).card = 3 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  have hprofile := orderSixtyFour_sizeTwo_muNegThree_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hfac := orderSixtyFour_sizeTwo_muNegThree_sameSign_defect_twoFactors
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hcrossPos (x : Xp) :
      ((Finset.univ : Finset Xm).filter fun y ↦ D.Adj x.1 y.1).card = 5 := by
    have himage :
        Finset.image Subtype.val
            ((Finset.univ : Finset Xm).filter fun y ↦ D.Adj x.1 y.1) =
          (D.neighborFinset x.1).filter fun y ↦ s y = -1 := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, D.mem_neighborFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.2.2⟩
      · rintro ⟨hxy, hsy⟩
        have hyc : y ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c y]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm.trans
            ((ConnectedComponent.mem_supp_iff c x.1).mp x.2.1)
        exact ⟨⟨y, hyc, hsy⟩, hxy, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Xm).filter fun y ↦ D.Adj x.1 y.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = ((D.neighborFinset x.1).filter fun y ↦ s y = -1).card :=
        congrArg Finset.card himage
      _ = 5 := (hprofile.2.2 x.1 x.2.1).1 x.2.2 |>.2.2.2
  have hcrossNeg (y : Xm) :
      ((Finset.univ : Finset Xp).filter fun x ↦ D.Adj x.1 y.1).card = 5 := by
    have himage :
        Finset.image Subtype.val
            ((Finset.univ : Finset Xp).filter fun x ↦ D.Adj x.1 y.1) =
          (D.neighborFinset y.1).filter fun x ↦ s x = 1 := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, D.mem_neighborFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz.symm, z.2.2⟩
      · rintro ⟨hyx, hsx⟩
        have hxc : x ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c x]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj hyx).symm.trans
            ((ConnectedComponent.mem_supp_iff c y.1).mp y.2.1)
        exact ⟨⟨x, hxc, hsx⟩, hyx.symm, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Xp).filter fun x ↦ D.Adj x.1 y.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = ((D.neighborFinset y.1).filter fun x ↦ s x = 1).card :=
        congrArg Finset.card himage
      _ = 5 := (hprofile.2.2 y.1 y.2.1).2 y.2.2 |>.2.2.2
  constructor
  · intro x
    have hpart := Finset.card_filter_add_card_filter_not
      (fun y : Xm ↦ D.Adj x.1 y.1) (s := Finset.univ)
    rw [hcrossPos x] at hpart
    rw [Finset.card_univ, hfac.2.1] at hpart
    change ((Finset.univ : Finset Xm).filter
      (fun y ↦ ¬ D.Adj x.1 y.1)).card = 3
    omega
  · intro y
    have hpart := Finset.card_filter_add_card_filter_not
      (fun x : Xp ↦ D.Adj x.1 y.1) (s := Finset.univ)
    rw [hcrossNeg y] at hpart
    rw [Finset.card_univ, hfac.1] at hpart
    change ((Finset.univ : Finset Xp).filter
      (fun x ↦ ¬ D.Adj x.1 y.1)).card = 3
    omega

/-- The cubic cross nondefect relation admits three pairwise-disjoint perfect
matchings between the positive and negative sign shores. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_threeMatchings
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
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegThreePositiveShore D c s
    let Xm := MuNegThreeNegativeShore D c s
    ∃ f g k : Xp ≃ Xm,
      (∀ x, ¬ D.Adj x.1 (f x).1) ∧
      (∀ x, ¬ D.Adj x.1 (g x).1) ∧
      (∀ x, ¬ D.Adj x.1 (k x).1) ∧
      (∀ x, f x ≠ g x) ∧ (∀ x, f x ≠ k x) ∧
      ∀ x, g x ≠ k x := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  let t : Xp → Finset Xm := fun x =>
    Finset.univ.filter fun y => ¬ D.Adj x.1 y.1
  have hcubic := orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_threeRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have ht : HallsTheoremOQ01OQ03.IsBiregular t 3 := by
    constructor
    · intro x
      exact hcubic.1 x
    · intro y
      simpa [t] using hcubic.2 y
  obtain ⟨f, g, k, hf, hg, hk, hfg, hfk, hgk⟩ :=
    exists_three_disjoint_equiv_of_three_biregular t ht
  refine ⟨f, g, k, ?_, ?_, ?_, hfg, hfk, hgk⟩
  · intro x
    exact (Finset.mem_filter.mp (hf x)).2
  · intro x
    exact (Finset.mem_filter.mp (hg x)).2
  · intro x
    exact (Finset.mem_filter.mp (hk x)).2

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_threeRegular
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_threeMatchings
