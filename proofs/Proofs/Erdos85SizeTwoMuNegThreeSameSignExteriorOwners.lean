import Proofs.Erdos85SizeTwoMuNegThreeExteriorOwnerPartition
import Proofs.Erdos85BinarySquareSizeTwoNegativeSupportProfiles
import Proofs.Erdos85NegativeSizeTwoThreeLevelAction

/-! # Same-sign exterior owner fibres at `mu = -3` -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

abbrev MuNegThreePositiveExteriorFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : V → ℤ) :=
  {z : V // (G.adjMatrix ℤ).mulVec s z + 2 * s z = 2}

abbrev MuNegThreeNegativeExteriorFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : V → ℤ) :=
  {z : V // (G.adjMatrix ℤ).mulVec s z + 2 * s z = -2}

/-- At `mu = -3`, the two extreme signed exterior fibres each have exactly
twelve vertices, and every vertex in either fibre lies outside the
distinguished size-two component. -/
theorem orderSixtyFour_sizeTwo_muNegThree_extremeExteriorFiber_profile
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
    Fintype.card (MuNegThreePositiveExteriorFiber G s) = 12 ∧
    Fintype.card (MuNegThreeNegativeExteriorFiber G s) = 12 ∧
    (∀ z : MuNegThreePositiveExteriorFiber G s, z.1 ∉ c.supp) ∧
    ∀ z : MuNegThreeNegativeExteriorFiber G s, z.1 ∉ c.supp := by
  classical
  let w : V → ℤ := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := (Finset.univ : Finset V).filter fun x => w x = 2
  let Sm := (Finset.univ : Finset V).filter fun x => w x = -2
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s (-3) hs_out hs_in hH hD
  have hsizes := negative_sizeTwo_support_sizes (-3) Sp.card Sm.card
    hprofile.1 hprofile.2.1 (Or.inr (Or.inl rfl))
  have hmid : (-3 : ℤ) = -3 ∧ Sp.card = 12 ∧ Sm.card = 12 := by
    rcases hsizes with hbad | hgood | hbad
    · omega
    · exact hgood
    · omega
  obtain ⟨-, hSpCard, hSmCard⟩ := hmid
  have hthree := orderSixtyFour_sizeTwo_signedJoint_threeLevelAction_of_local
    G hfree hreg hcard c hc s (-3) hs_out hs_in hH hD
  have hSpOut : ∀ x ∈ Sp, x ∉ c.supp := by
    intro x hx hxc
    have hw0 := hthree.1 x hxc
    have hw2 : w x = 2 := (Finset.mem_filter.mp hx).2
    change w x = 0 at hw0
    omega
  have hSmOut : ∀ x ∈ Sm, x ∉ c.supp := by
    intro x hx hxc
    have hw0 := hthree.1 x hxc
    have hwm2 : w x = -2 := (Finset.mem_filter.mp hx).2
    change w x = 0 at hw0
    omega
  have hpCard : Fintype.card (MuNegThreePositiveExteriorFiber G s) = 12 := by
    rw [Fintype.card_subtype]
    change Sp.card = 12
    exact hSpCard
  have hmCard : Fintype.card (MuNegThreeNegativeExteriorFiber G s) = 12 := by
    rw [Fintype.card_subtype]
    change Sm.card = 12
    exact hSmCard
  refine ⟨hpCard, hmCard, ?_, ?_⟩
  · intro z
    apply hSpOut z.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩
  · intro z
    apply hSmOut z.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩

/-- The two twelve-vertex extreme fibres are exactly the two same-sign
component-neighbour profiles: `2+0` and `0+2`. -/
theorem orderSixtyFour_sizeTwo_muNegThree_extremeExteriorFiber_neighborProfile
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
    (∀ z : MuNegThreePositiveExteriorFiber G s,
      ((Finset.univ : Finset Xp).filter fun x ↦ G.Adj x.1 z.1).card = 2 ∧
      ((Finset.univ : Finset Xm).filter fun x ↦ G.Adj x.1 z.1).card = 0) ∧
    ∀ z : MuNegThreeNegativeExteriorFiber G s,
      ((Finset.univ : Finset Xp).filter fun x ↦ G.Adj x.1 z.1).card = 0 ∧
      ((Finset.univ : Finset Xm).filter fun x ↦ G.Adj x.1 z.1).card = 2 := by
  classical
  dsimp only
  let A := G.adjMatrix ℤ
  let w : V → ℤ := fun x => A.mulVec s x + 2 * s x
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-3) hs_out hs_in hH hD
  have hextreme := orderSixtyFour_sizeTwo_muNegThree_extremeExteriorFiber_profile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hcolumn (z : V) (hzout : z ∉ c.supp) (hw : w z = 2 ∨ w z = -2) :
      (((Finset.univ : Finset Xp).filter fun x ↦ G.Adj x.1 z).card,
       ((Finset.univ : Finset Xm).filter fun x ↦ G.Adj x.1 z).card) =
        if w z = 2 then (2, 0) else (0, 2) := by
    let C := (G.neighborFinset z).filter fun x => D.connectedComponentMk x = c
    let Cp := C.filter fun x => s x = 1
    let Cm := C.filter fun x => s x = -1
    have hmem : ∀ x, x ∈ c.supp ↔ D.connectedComponentMk x = c :=
      fun x => ConnectedComponent.mem_supp_iff c x
    have hCcard : C.card = 2 := P.componentNeighborCard z
    have hcover : C = Cp ∪ Cm := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Cp, Cm]
      constructor
      · intro hx
        have hxc : x ∈ c.supp := (hmem x).mpr (Finset.mem_filter.mp hx).2
        rcases hs_in x hxc with hm | hp
        · exact Or.inr ⟨hx, hm⟩
        · exact Or.inl ⟨hx, hp⟩
      · rintro (hx | hx) <;> exact hx.1
    have hdisj : Disjoint Cp Cm := by
      rw [Finset.disjoint_left]
      intro x hp hm
      have hp' := (Finset.mem_filter.mp hp).2
      have hm' := (Finset.mem_filter.mp hm).2
      omega
    have hcards : Cp.card + Cm.card = 2 := by
      rw [← Finset.card_union_of_disjoint hdisj, ← hcover, hCcard]
    have hsumFull : ∑ x ∈ G.neighborFinset z, s x = w z := by
      rw [← SimpleGraph.adjMatrix_mulVec_apply]
      have hsz : s z = 0 := hs_out z hzout
      simp [w, A, hsz]
    have hsumC : ∑ x ∈ C, s x = w z := by
      rw [← hsumFull]
      symm
      rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset z)
        (fun x => D.connectedComponentMk x = c)]
      have houtzero : ∑ x ∈ (G.neighborFinset z).filter
          (fun x => ¬ D.connectedComponentMk x = c), s x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        apply hs_out x
        intro hxc
        exact (Finset.mem_filter.mp hx).2 ((hmem x).mp hxc)
      rw [houtzero, add_zero]
    have hsumSplit : (Cp.card : ℤ) - Cm.card = w z := by
      rw [hcover, Finset.sum_union hdisj] at hsumC
      have hp : ∑ x ∈ Cp, s x = (Cp.card : ℤ) := by
        calc
          _ = ∑ _x ∈ Cp, (1 : ℤ) := Finset.sum_congr rfl
            (fun x hx => (Finset.mem_filter.mp hx).2)
          _ = _ := by simp
      have hm : ∑ x ∈ Cm, s x = -(Cm.card : ℤ) := by
        calc
          _ = ∑ _x ∈ Cm, (-1 : ℤ) := Finset.sum_congr rfl
            (fun x hx => (Finset.mem_filter.mp hx).2)
          _ = _ := by simp
      rw [hp, hm] at hsumC
      exact hsumC
    have hXp : Finset.image Subtype.val
        ((Finset.univ : Finset Xp).filter fun x => G.Adj x.1 z) = Cp := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, Cp, C]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨(G.mem_neighborFinset _ _).mpr hy.symm,
          (hmem y.1).mp y.2.1⟩, y.2.2⟩
      · rintro ⟨⟨hxz, hxc⟩, hsx⟩
        exact ⟨⟨x, (hmem x).mpr hxc, hsx⟩,
          ((G.mem_neighborFinset _ _).mp hxz).symm, rfl⟩
    have hXm : Finset.image Subtype.val
        ((Finset.univ : Finset Xm).filter fun x => G.Adj x.1 z) = Cm := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, Cm, C]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨(G.mem_neighborFinset _ _).mpr hy.symm,
          (hmem y.1).mp y.2.1⟩, y.2.2⟩
      · rintro ⟨⟨hxz, hxc⟩, hsx⟩
        exact ⟨⟨x, (hmem x).mpr hxc, hsx⟩,
          ((G.mem_neighborFinset _ _).mp hxz).symm, rfl⟩
    have hpCard : ((Finset.univ : Finset Xp).filter
        fun x ↦ G.Adj x.1 z).card = Cp.card := by
      rw [← hXp, Finset.card_image_of_injective _ Subtype.val_injective]
    have hmCard : ((Finset.univ : Finset Xm).filter
        fun x ↦ G.Adj x.1 z).card = Cm.card := by
      rw [← hXm, Finset.card_image_of_injective _ Subtype.val_injective]
    split_ifs with hpos
    · rw [hpCard, hmCard]
      apply Prod.ext <;> omega
    · rw [hpCard, hmCard]
      rcases hw with hw | hw
      · exact (hpos hw).elim
      · apply Prod.ext <;> omega
  constructor
  · intro z
    have hzout := hextreme.2.2.1 z
    have hc := hcolumn z.1 hzout (Or.inl z.2)
    have hwpos : w z.1 = 2 := z.2
    rw [if_pos hwpos] at hc
    have hp := congrArg Prod.fst hc
    have hm := congrArg Prod.snd hc
    exact ⟨hp, hm⟩
  · intro z
    have hzout := hextreme.2.2.2 z
    have hc := hcolumn z.1 hzout (Or.inr z.2)
    have hwneg : w z.1 = -2 := z.2
    have hnpos : w z.1 ≠ 2 := by omega
    rw [if_neg hnpos] at hc
    have hp := congrArg Prod.fst hc
    have hm := congrArg Prod.snd hc
    exact ⟨hp, hm⟩

/-- The two twelve-vertex extreme fibres are exactly the 24-vertex
complement of the cross-owner set in the exterior. -/
theorem orderSixtyFour_sizeTwo_muNegThree_extremeFibers_eq_sameSignOwnerHalf
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
    let w := fun z => (G.adjMatrix ℤ).mulVec s z + 2 * s z
    let Sp := (Finset.univ : Finset V).filter fun z ↦ w z = 2
    let Sm := (Finset.univ : Finset V).filter fun z ↦ w z = -2
    Sp ∪ Sm = componentExteriorFinset c \ N.crossOwnerFinset G c s := by
  classical
  dsimp only
  let w := fun z => (G.adjMatrix ℤ).mulVec s z + 2 * s z
  let Sp := (Finset.univ : Finset V).filter fun z ↦ w z = 2
  let Sm := (Finset.univ : Finset V).filter fun z ↦ w z = -2
  have hextreme := orderSixtyFour_sizeTwo_muNegThree_extremeExteriorFiber_profile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hneighbors :=
    orderSixtyFour_sizeTwo_muNegThree_extremeExteriorFiber_neighborProfile
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hsub : Sp ∪ Sm ⊆ componentExteriorFinset c \ N.crossOwnerFinset G c s := by
    intro z hz
    rcases Finset.mem_union.mp hz with hp | hm
    · let zp : MuNegThreePositiveExteriorFiber G s :=
        ⟨z, (Finset.mem_filter.mp hp).2⟩
      have hzout := hextreme.2.2.1 zp
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, ?_⟩
      · change z ∈ Finset.univ.filter (fun z ↦ z ∉ c.supp)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzout⟩
      · intro hcross
        obtain ⟨-, x, y, hxy⟩ :=
          (N.mem_crossOwnerFinset_iff G hfree c s z).mp hcross
        have hymem : y ∈ (Finset.univ.filter fun y :
            MuNegThreeNegativeShore (secondOrderDefectGraph G) c s ↦
              G.Adj y.1 z) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.2⟩
        have hempty := Finset.card_eq_zero.mp (hneighbors.1 zp).2
        rw [hempty] at hymem
        simp at hymem
    · let zm : MuNegThreeNegativeExteriorFiber G s :=
        ⟨z, (Finset.mem_filter.mp hm).2⟩
      have hzout := hextreme.2.2.2 zm
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, ?_⟩
      · change z ∈ Finset.univ.filter (fun z ↦ z ∉ c.supp)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzout⟩
      · intro hcross
        obtain ⟨-, x, y, hxy⟩ :=
          (N.mem_crossOwnerFinset_iff G hfree c s z).mp hcross
        have hxmem : x ∈ (Finset.univ.filter fun x :
            MuNegThreePositiveShore (secondOrderDefectGraph G) c s ↦
              G.Adj x.1 z) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.1⟩
        have hempty := Finset.card_eq_zero.mp (hneighbors.2 zm).1
        rw [hempty] at hxmem
        simp at hxmem
  have hSp : Sp.card = 12 := by
    simpa [Sp, w, Fintype.card_subtype] using hextreme.1
  have hSm : Sm.card = 12 := by
    simpa [Sm, w, Fintype.card_subtype] using hextreme.2.1
  have hdisj : Disjoint Sp Sm := by
    rw [Finset.disjoint_left]
    intro z hp hm
    have hp' := (Finset.mem_filter.mp hp).2
    have hm' := (Finset.mem_filter.mp hm).2
    omega
  have hleft : (Sp ∪ Sm).card = 24 := by
    rw [Finset.card_union_of_disjoint hdisj, hSp, hSm]
  have hright : (componentExteriorFinset c \ N.crossOwnerFinset G c s).card = 24 :=
    N.exterior_sdiff_crossOwner_card_twentyFour
      G hfree hreg hcard c hc s hshore
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hleft, hright])

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_extremeExteriorFiber_profile
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_extremeExteriorFiber_neighborProfile
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_extremeFibers_eq_sameSignOwnerHalf
