import Proofs.Erdos85SizeTwoMuNegOneExtremeShadows
import Proofs.Erdos85SizeTwoMuNegOneInternalStructure
import Proofs.Erdos85TwoIncidenceShadowRegular
import Proofs.Erdos85ExteriorDefectDecomposition

/-! # The `3 + 2 + 2` shore-edge decomposition at `mu = -1` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Ambient adjacency across the two sign shores is two-biregular; its
common-neighbor shadows on the individual shores are therefore 2-regular. -/
theorem orderSixtyFour_sizeTwo_muNegOne_internal_shadows_twoRegular
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
        s y = (-1 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegOnePositiveShore D c s
    let Xm := MuNegOneNegativeShore D c s
    let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
    (∀ x, (twoIncidenceShadow B).degree x = 2) ∧
      ∀ y, (twoIncidenceShadow (fun z x => B x z)).degree y = 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegOnePositiveShore D c s
  let Xm := MuNegOneNegativeShore D c s
  let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
  have hprofile := orderSixtyFour_sizeTwo_muNegOne_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hmem : ∀ x, x ∈ c.supp ↔ D.connectedComponentMk x = c :=
    fun x => ConnectedComponent.mem_supp_iff c x
  have hrow : ∀ x : Xp,
      ((Finset.univ : Finset Xm).filter fun y => B x y).card = 2 := by
    intro x
    let C := (G.neighborFinset x.1).filter fun y => D.connectedComponentMk y = c
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
        exact ⟨⟨y, (hmem y).mpr hyc, hsy⟩,
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
    let C := (G.neighborFinset y.1).filter fun x => D.connectedComponentMk x = c
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
        exact ⟨⟨x, (hmem x).mpr hxc, hsx⟩,
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
    apply Subtype.ext
    exact Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1
        (fun h => hxy (Subtype.ext h))) z.1 (by
          simp [B] at hxz hyz ⊢
          exact ⟨hxz, hyz⟩) w.1 (by
          simp [B] at hxw hyw ⊢
          exact ⟨hxw, hyw⟩)
  have hpairM : ∀ ⦃x y z w⦄, x ≠ y →
      B z x → B z y → B w x → B w y → z = w := by
    intro x y z w hxy hzx hzy hwx hwy
    apply Subtype.ext
    apply Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1
        (fun h => hxy (Subtype.ext h)))
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hzx.symm,
        (G.mem_neighborFinset _ _).mpr hzy.symm⟩
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hwx.symm,
        (G.mem_neighborFinset _ _).mpr hwy.symm⟩
  exact ⟨twoIncidenceShadow_regular B 2 hrow hcol hpairP,
    twoIncidenceShadow_regular (fun z x => B x z) 2 hcol hrow hpairM⟩

/-- On eight vertices, pairwise edge-disjoint regular factors of degrees
`3`, `2`, and `2` exhaust the complete graph. -/
theorem three_two_two_regular_partition_complete
    {X : Type*} [Fintype X] [DecidableEq X]
    (A B C : SimpleGraph X)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (hcard : Fintype.card X = 8)
    (hA : ∀ x, A.degree x = 3)
    (hB : ∀ x, B.degree x = 2)
    (hC : ∀ x, C.degree x = 2)
    (hAB : ∀ ⦃x y⦄, A.Adj x y → ¬ B.Adj x y)
    (hAC : ∀ ⦃x y⦄, A.Adj x y → ¬ C.Adj x y)
    (hBC : ∀ ⦃x y⦄, B.Adj x y → ¬ C.Adj x y) :
    (A ⊔ B) ⊔ C = ⊤ := by
  classical
  ext x y
  constructor
  · intro _
    simp only [SimpleGraph.top_adj]
    intro hxy
    subst y
    simp at *
  · intro hxy
    have hne : x ≠ y := by simpa using hxy
    let NA := A.neighborFinset x
    let NB := B.neighborFinset x
    let NC := C.neighborFinset x
    let U := (NA ∪ NB) ∪ NC
    have hdAB : Disjoint NA NB := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      exact hAB ((A.mem_neighborFinset x z).mp hzA)
        ((B.mem_neighborFinset x z).mp hzB)
    have hdAC : Disjoint NA NC := by
      rw [Finset.disjoint_left]
      intro z hzA hzC
      exact hAC ((A.mem_neighborFinset x z).mp hzA)
        ((C.mem_neighborFinset x z).mp hzC)
    have hdBC : Disjoint NB NC := by
      rw [Finset.disjoint_left]
      intro z hzB hzC
      exact hBC ((B.mem_neighborFinset x z).mp hzB)
        ((C.mem_neighborFinset x z).mp hzC)
    have hdU : Disjoint (NA ∪ NB) NC :=
      Finset.disjoint_union_left.mpr ⟨hdAC, hdBC⟩
    have hUcard : U.card = 7 := by
      dsimp [U]
      rw [Finset.card_union_of_disjoint hdU,
        Finset.card_union_of_disjoint hdAB]
      change A.degree x + B.degree x + C.degree x = 7
      rw [hA x, hB x, hC x]
    have hUsub : U ⊆ Finset.univ.erase x := by
      intro z hz
      simp only [U, Finset.mem_union] at hz
      have hzx : z ≠ x := by
        rcases hz with (hz | hz) | hz
        · exact (A.ne_of_adj ((A.mem_neighborFinset x z).mp hz)).symm
        · exact (B.ne_of_adj ((B.mem_neighborFinset x z).mp hz)).symm
        · exact (C.ne_of_adj ((C.mem_neighborFinset x z).mp hz)).symm
      simp [hzx]
    have herase : (Finset.univ.erase x : Finset X).card = 7 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]
    have hUeq : U = Finset.univ.erase x :=
      Finset.eq_of_subset_of_card_le hUsub (by omega)
    have hyU : y ∈ U := by
      rw [hUeq]
      simp [hne.symm]
    simp only [U, Finset.mem_union] at hyU
    rcases hyU with (hyA | hyB) | hyC
    · exact Or.inl (Or.inl ((A.mem_neighborFinset x y).mp hyA))
    · exact Or.inl (Or.inr ((B.mem_neighborFinset x y).mp hyB))
    · exact Or.inr ((C.mem_neighborFinset x y).mp hyC)

/-- A defect edge cannot also be induced by a common ambient neighbor. -/
theorem muNegOne_defect_comap_disjoint_twoIncidenceShadow
    {V X Z : Type*} [Fintype V] [Fintype X] [Fintype Z]
    [DecidableEq V] [DecidableEq X] [DecidableEq Z]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (f : X → V) (hf : Function.Injective f)
    (g : Z → V) (R : X → Z → Prop) [DecidableRel R]
    (hR : ∀ x z, R x z → G.Adj (f x) (g z)) :
    ∀ ⦃x y⦄, ((secondOrderDefectGraph G).comap f).Adj x y →
      ¬ (twoIncidenceShadow R).Adj x y := by
  intro x y hxy
  rintro ⟨hne, z, hxz, hyz⟩
  have hzero := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
    G hfree (fun h ↦ hne (hf h))).mp hxy
  have hzmem : g z ∈ G.neighborFinset (f x) ∩ G.neighborFinset (f y) :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (hR x z hxz),
      (G.mem_neighborFinset _ _).mpr (hR y z hyz)⟩
  rw [Finset.card_eq_zero.mp hzero] at hzmem
  simp at hzmem

/-- On either sign shore, the cubic defect factor, internal common-neighbor
two-factor, and extreme-owner two-factor partition all edges of `K₈`. -/
theorem orderSixtyFour_sizeTwo_muNegOne_shore_edge_partitions
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
        s y = (-1 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegOnePositiveShore D c s
    let Xm := MuNegOneNegativeShore D c s
    let B : Xp → Xm → Prop := fun x y ↦ G.Adj x.1 y.1
    let Rp : Xp → MuNegOnePositiveExteriorFiber G s → Prop :=
      fun x z ↦ G.Adj x.1 z.1
    let Rm : Xm → MuNegOneNegativeExteriorFiber G s → Prop :=
      fun x z ↦ G.Adj x.1 z.1
    (((D.comap Subtype.val ⊔ twoIncidenceShadow B) ⊔
        twoIncidenceShadow Rp) = ⊤) ∧
      (((D.comap Subtype.val ⊔ twoIncidenceShadow (fun y x ↦ B x y)) ⊔
        twoIncidenceShadow Rm) = ⊤) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegOnePositiveShore D c s
  let Xm := MuNegOneNegativeShore D c s
  let Ep := MuNegOnePositiveExteriorFiber G s
  let Em := MuNegOneNegativeExteriorFiber G s
  let B : Xp → Xm → Prop := fun x y ↦ G.Adj x.1 y.1
  let Rp : Xp → Ep → Prop := fun x z ↦ G.Adj x.1 z.1
  let Rm : Xm → Em → Prop := fun x z ↦ G.Adj x.1 z.1
  let Dp := D.comap (fun x : Xp ↦ x.1)
  let Dm := D.comap (fun x : Xm ↦ x.1)
  have hprofile := orderSixtyFour_sizeTwo_muNegOne_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hint := orderSixtyFour_sizeTwo_muNegOne_internal_shadows_twoRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hext := orderSixtyFour_sizeTwo_muNegOne_extremeOwner_shadows_twoRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hinc := orderSixtyFour_sizeTwo_muNegOne_extremeIncidence_twoRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have howner := orderSixtyFour_sizeTwo_muNegOne_extremeOwner_profile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hDpdeg : ∀ x, Dp.degree x = 3 := by
    intro x
    rw [← Dp.card_neighborFinset_eq_degree]
    have heq : Dp.neighborFinset x =
        (Finset.univ : Finset Xp).filter (fun y ↦ D.Adj x.1 y.1) := by
      ext y
      simp [Dp]
    rw [heq]
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset Xp).filter fun y ↦ D.Adj x.1 y.1) =
        (D.neighborFinset x.1).filter fun y ↦ s y = 1 := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(D.mem_neighborFinset _ _).mpr hz, z.2.2⟩
      · rintro ⟨hxy, hsy⟩
        have hyc : y ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c, ← x.2.1]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj
            ((D.mem_neighborFinset _ _).mp hxy)).symm
        exact ⟨⟨y, hyc, hsy⟩, (D.mem_neighborFinset _ _).mp hxy, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Xp).filter fun y ↦ D.Adj x.1 y.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = _ := congrArg Finset.card himage
      _ = 3 := (hprofile.2.2 x.1 x.2.1).1 x.2.2 |>.2.2.1
  have hDmdeg : ∀ x, Dm.degree x = 3 := by
    intro x
    rw [← Dm.card_neighborFinset_eq_degree]
    have heq : Dm.neighborFinset x =
        (Finset.univ : Finset Xm).filter (fun y ↦ D.Adj x.1 y.1) := by
      ext y
      simp [Dm]
    rw [heq]
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset Xm).filter fun y ↦ D.Adj x.1 y.1) =
        (D.neighborFinset x.1).filter fun y ↦ s y = -1 := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(D.mem_neighborFinset _ _).mpr hz, z.2.2⟩
      · rintro ⟨hxy, hsy⟩
        have hyc : y ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c, ← x.2.1]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj
            ((D.mem_neighborFinset _ _).mp hxy)).symm
        exact ⟨⟨y, hyc, hsy⟩, (D.mem_neighborFinset _ _).mp hxy, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Xm).filter fun y ↦ D.Adj x.1 y.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = _ := congrArg Finset.card himage
      _ = 3 := (hprofile.2.2 x.1 x.2.1).2 x.2.2 |>.2.2.1
  have hinternal_exterior_p : ∀ ⦃x y⦄,
      (twoIncidenceShadow B).Adj x y → ¬ (twoIncidenceShadow Rp).Adj x y := by
    rintro x y ⟨hne, z, hxz, hyz⟩ ⟨-, w, hxw, hyw⟩
    have heq : z.1 = w.1 := Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1
        (fun h ↦ hne (Subtype.ext h))) z.1
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxz,
        (G.mem_neighborFinset _ _).mpr hyz⟩) w.1
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxw,
        (G.mem_neighborFinset _ _).mpr hyw⟩)
    exact (howner.2.2.1 w).1 (heq ▸ z.2.1)
  have hinternal_exterior_m : ∀ ⦃x y⦄,
      (twoIncidenceShadow (fun y x ↦ B x y)).Adj x y →
        ¬ (twoIncidenceShadow Rm).Adj x y := by
    rintro x y ⟨hne, z, hxz, hyz⟩ ⟨-, w, hxw, hyw⟩
    have heq : z.1 = w.1 := Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1
        (fun h ↦ hne (Subtype.ext h))) z.1
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxz.symm,
        (G.mem_neighborFinset _ _).mpr hyz.symm⟩) w.1
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxw,
        (G.mem_neighborFinset _ _).mpr hyw⟩)
    exact (howner.2.2.2 w).1 (heq ▸ z.2.1)
  constructor
  · exact three_two_two_regular_partition_complete Dp
      (twoIncidenceShadow B) (twoIncidenceShadow Rp) hinc.1 hDpdeg
      hint.1 hext.1
      (muNegOne_defect_comap_disjoint_twoIncidenceShadow G hfree Subtype.val
        Subtype.val_injective Subtype.val B (fun _ _ h ↦ h))
      (muNegOne_defect_comap_disjoint_twoIncidenceShadow G hfree Subtype.val
        Subtype.val_injective Subtype.val Rp (fun _ _ h ↦ h))
      hinternal_exterior_p
  · exact three_two_two_regular_partition_complete Dm
      (twoIncidenceShadow (fun y x ↦ B x y)) (twoIncidenceShadow Rm)
      hinc.2.1 hDmdeg hint.2 hext.2
      (muNegOne_defect_comap_disjoint_twoIncidenceShadow G hfree Subtype.val
        Subtype.val_injective Subtype.val (fun y x ↦ B x y)
        (fun _ _ h ↦ h.symm))
      (muNegOne_defect_comap_disjoint_twoIncidenceShadow G hfree Subtype.val
        Subtype.val_injective Subtype.val Rm (fun _ _ h ↦ h))
      hinternal_exterior_m

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_internal_shadows_twoRegular
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_shore_edge_partitions
