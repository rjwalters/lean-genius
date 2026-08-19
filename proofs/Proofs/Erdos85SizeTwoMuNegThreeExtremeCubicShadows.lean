import Proofs.Erdos85SizeTwoMuNegThreeExteriorIncidence
import Proofs.Erdos85TwoIncidenceShadowRegular

/-! # Cubic shore shadows of the `mu = -3` extreme owner fibres -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Suppressing the twelve degree-two positive extreme owners gives a cubic
simple graph on the eight-point positive shore; the negative fibre gives the
same conclusion on the negative shore. -/
theorem orderSixtyFour_sizeTwo_muNegThree_extremeOwner_shadows_cubic
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
        s y = (-3 : ℤ) * s z)
    (N : MuNegThreeCrossOwnerNormalForm G c s)
    (hshore : Fintype.card
      (MuNegThreePositiveShore (secondOrderDefectGraph G) c s) = 8) :
    let Xp := MuNegThreePositiveShore (secondOrderDefectGraph G) c s
    let Xm := MuNegThreeNegativeShore (secondOrderDefectGraph G) c s
    let Zp := MuNegThreePositiveExteriorFiber G s
    let Zm := MuNegThreeNegativeExteriorFiber G s
    let Rp : Xp → Zp → Prop := fun x z ↦ G.Adj x.1 z.1
    let Rm : Xm → Zm → Prop := fun x z ↦ G.Adj x.1 z.1
    (∀ x, (twoIncidenceShadow Rp).degree x = 3) ∧
      ∀ x, (twoIncidenceShadow Rm).degree x = 3 := by
  classical
  dsimp only
  let Xp := MuNegThreePositiveShore (secondOrderDefectGraph G) c s
  let Xm := MuNegThreeNegativeShore (secondOrderDefectGraph G) c s
  let Zp := MuNegThreePositiveExteriorFiber G s
  let Zm := MuNegThreeNegativeExteriorFiber G s
  let Rp : Xp → Zp → Prop := fun x z ↦ G.Adj x.1 z.1
  let Rm : Xm → Zm → Prop := fun x z ↦ G.Adj x.1 z.1
  have hneighbors :=
    orderSixtyFour_sizeTwo_muNegThree_extremeExteriorFiber_neighborProfile
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hrowp : ∀ x : Xp,
      ((Finset.univ : Finset Zp).filter fun z ↦ Rp x z).card = 3 := by
    intro x
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset Zp).filter fun z ↦ Rp x z) =
        ((Finset.univ : Finset V).filter fun z ↦
          (G.adjMatrix ℤ).mulVec s z + 2 * s z = 2).filter
            (fun z ↦ G.Adj x.1 z) := by
      ext z
      simp [Rp, Zp, and_comm]
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Zp).filter fun z ↦ Rp x z)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = _ := congrArg Finset.card himage
      _ = 3 := N.positive_extreme_neighbors_card_three
        G hfree hreg hcard c hc s hs_out hs_in hH hD hshore x
  have hrowm : ∀ x : Xm,
      ((Finset.univ : Finset Zm).filter fun z ↦ Rm x z).card = 3 := by
    intro x
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset Zm).filter fun z ↦ Rm x z) =
        ((Finset.univ : Finset V).filter fun z ↦
          (G.adjMatrix ℤ).mulVec s z + 2 * s z = -2).filter
            (fun z ↦ G.Adj x.1 z) := by
      ext z
      simp [Rm, Zm, and_comm]
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Zm).filter fun z ↦ Rm x z)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = _ := congrArg Finset.card himage
      _ = 3 := N.negative_extreme_neighbors_card_three
        G hfree hreg hcard c hc s hs_out hs_in hH hD hshore x
  have hcolp : ∀ z : Zp,
      ((Finset.univ : Finset Xp).filter fun x ↦ Rp x z).card = 2 := by
    intro z
    exact (hneighbors.1 z).1
  have hcolm : ∀ z : Zm,
      ((Finset.univ : Finset Xm).filter fun x ↦ Rm x z).card = 2 := by
    intro z
    exact (hneighbors.2 z).2
  have hpairp : ∀ ⦃x y : Xp⦄ ⦃z w : Zp⦄, x ≠ y →
      Rp x z → Rp y z → Rp x w → Rp y w → z = w := by
    intro x y z w hxy hxz hyz hxw hyw
    apply Subtype.ext
    have hxyval : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
    apply Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1 hxyval)
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxz,
        (G.mem_neighborFinset _ _).mpr hyz⟩
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxw,
        (G.mem_neighborFinset _ _).mpr hyw⟩
  have hpairm : ∀ ⦃x y : Xm⦄ ⦃z w : Zm⦄, x ≠ y →
      Rm x z → Rm y z → Rm x w → Rm y w → z = w := by
    intro x y z w hxy hxz hyz hxw hyw
    apply Subtype.ext
    have hxyval : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
    apply Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1 hxyval)
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxz,
        (G.mem_neighborFinset _ _).mpr hyz⟩
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxw,
        (G.mem_neighborFinset _ _).mpr hyw⟩
  exact ⟨twoIncidenceShadow_regular Rp 3 hrowp hcolp hpairp,
    twoIncidenceShadow_regular Rm 3 hrowm hcolm hpairm⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_extremeOwner_shadows_cubic
