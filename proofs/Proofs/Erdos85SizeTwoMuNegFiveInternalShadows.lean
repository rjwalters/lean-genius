import Proofs.Erdos85TwoIncidenceShadowRegular
import Proofs.Erdos85SizeTwoMuNegFiveMatchingNormalization

/-!
# Internal bipartite shore shadows at `mu=-5`

Ambient adjacency inside the sixteen-component is a two-regular bipartite
relation between the two sign shores.  Its common-neighbor shadow on either
shore is therefore a two-regular graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem orderSixtyFour_sizeTwo_muNegFive_internal_shadows_twoRegular
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
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Xm := MuNegFiveNegativeShore D c s
    let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
    (∀ x, (twoIncidenceShadow B).degree x = 2) ∧
      ∀ y, (twoIncidenceShadow (fun z x => B x z)).degree y = 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
  have hprofile := orderSixtyFour_sizeTwo_muNegFive_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hmem : ∀ x, x ∈ c.supp ↔ D.connectedComponentMk x = c :=
    fun x => ConnectedComponent.mem_supp_iff c x
  have hrow : ∀ x : Xp,
      ((Finset.univ : Finset Xm).filter fun y => B x y).card = 2 := by
    intro x
    let C := (G.neighborFinset x.1).filter
      (fun y => D.connectedComponentMk y = c)
    let T := C.filter fun y => s y = -1
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset Xm).filter fun y => B x y) = T := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, B, T, C]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨(G.mem_neighborFinset _ _).mpr hz,
          (hmem z.1).mp z.2.1⟩, z.2.2⟩
      · rintro ⟨⟨hxy, hyc⟩, hsy⟩
        refine ⟨⟨y, (hmem y).mpr hyc, hsy⟩,
          (G.mem_neighborFinset _ _).mp hxy, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Xm).filter fun y => B x y)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = T.card := congrArg Finset.card himage
      _ = 2 := (hprofile.2.2 x.1 x.2.1).1 x.2.2 |>.2.1
  have hcol : ∀ y : Xm,
      ((Finset.univ : Finset Xp).filter fun x => B x y).card = 2 := by
    intro y
    let C := (G.neighborFinset y.1).filter
      (fun x => D.connectedComponentMk x = c)
    let T := C.filter fun x => s x = 1
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset Xp).filter fun x => B x y) = T := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, B, T, C]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨(G.mem_neighborFinset _ _).mpr hz.symm,
          (hmem z.1).mp z.2.1⟩, z.2.2⟩
      · rintro ⟨⟨hxy, hxc⟩, hsx⟩
        refine ⟨⟨x, (hmem x).mpr hxc, hsx⟩,
          ((G.mem_neighborFinset _ _).mp hxy).symm, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Xp).filter fun x => B x y)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = T.card := congrArg Finset.card himage
      _ = 2 := (hprofile.2.2 y.1 y.2.1).2 y.2.2 |>.2.1
  have hpairP : ∀ ⦃x y z w⦄, x ≠ y →
      B x z → B y z → B x w → B y w → z = w := by
    intro x y z w hxy hxz hyz hxw hyw
    change G.Adj x.1 z.1 at hxz
    change G.Adj y.1 z.1 at hyz
    change G.Adj x.1 w.1 at hxw
    change G.Adj y.1 w.1 at hyw
    apply Subtype.ext
    exact Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1
        (fun h => hxy (Subtype.ext h))) z.1 (by simp [hxz, hyz])
        w.1 (by simp [hxw, hyw])
  have hpairM : ∀ ⦃x y z w⦄, x ≠ y →
      B z x → B z y → B w x → B w y → z = w := by
    intro x y z w hxy hzx hzy hwx hwy
    change G.Adj z.1 x.1 at hzx
    change G.Adj z.1 y.1 at hzy
    change G.Adj w.1 x.1 at hwx
    change G.Adj w.1 y.1 at hwy
    apply Subtype.ext
    exact Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1
        (fun h => hxy (Subtype.ext h))) z.1
        (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr hzx.symm,
            (G.mem_neighborFinset _ _).mpr hzy.symm⟩)
        w.1 (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr hwx.symm,
            (G.mem_neighborFinset _ _).mpr hwy.symm⟩)
  exact ⟨twoIncidenceShadow_regular B 2 hrow hcol hpairP,
    twoIncidenceShadow_regular (fun z x => B x z) 2 hcol hrow hpairM⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_internal_shadows_twoRegular
