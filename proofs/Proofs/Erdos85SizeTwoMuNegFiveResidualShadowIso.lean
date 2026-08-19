import Proofs.Erdos85BipartiteTwoRegularHall
import Proofs.Erdos85BipartiteTwoRegularShadowIso
import Proofs.Erdos85SizeTwoMuNegFiveMatchingNormalization

/-! # Isomorphism of the `mu=-5` internal shore shadows -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem orderSixtyFour_sizeTwo_muNegFive_internal_shadows_iso
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
    Nonempty (twoIncidenceShadow B ≃g
      twoIncidenceShadow (fun y x => B x y)) := by
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
  obtain ⟨f, hf⟩ := twoRegularBipartite_exists_afterMatching B hrow hcol
  exact ⟨hf.shadowIso⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_internal_shadows_iso
