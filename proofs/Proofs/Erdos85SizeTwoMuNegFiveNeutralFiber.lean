import Proofs.Erdos85NegativeSizeTwoMuNegFiveRowSaturation
import Proofs.Erdos85SizeTwoMuNegFiveSignedStructure
import Proofs.Erdos85SizeTwoMuNegFiveMatchingNormalization

/-! # The neutral exterior fiber at `mu=-5` -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

abbrev MuNegFiveNeutralFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ) :=
  {z : V // z ∉ c.supp ∧ (G.adjMatrix ℤ).mulVec s z + 2 * s z = 0}

/-- The zero-level exterior fiber has order sixteen.  Every vertex in it has
exactly one ambient neighbor on each sign shore of the distinguished
component. -/
theorem orderSixtyFour_sizeTwo_muNegFive_neutralFiber_profile
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
    let S0 := MuNegFiveNeutralFiber G c s
    Fintype.card S0 = 16 ∧
      (∀ z : S0,
        ((Finset.univ : Finset Xp).filter fun x => G.Adj x.1 z.1).card = 1) ∧
      ∀ z : S0,
        ((Finset.univ : Finset Xm).filter fun x => G.Adj x.1 z.1).card = 1 := by
  classical
  dsimp only
  let A := G.adjMatrix ℤ
  let w : V → ℤ := fun x => A.mulVec s x + 2 * s x
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let S0 := MuNegFiveNeutralFiber G c s
  let Sp := (Finset.univ : Finset V).filter fun x => w x = 2
  let Sm := (Finset.univ : Finset V).filter fun x => w x = -2
  let Z0 := (Finset.univ : Finset V).filter fun x => x ∉ c.supp ∧ w x = 0
  let O := (Finset.univ : Finset V).filter fun x => x ∉ c.supp
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  have hthree := orderSixtyFour_sizeTwo_signedJoint_threeLevelAction_of_local
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  have hsupport := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  have hSpCard : Sp.card = 16 := by
    have hsizes := negative_sizeTwo_support_sizes (-5) Sp.card Sm.card
      hsupport.1 hsupport.2.1 (Or.inr (Or.inr rfl))
    rcases hsizes with h | h | h
    · omega
    · omega
    · exact h.2.1
  have hSmCard : Sm.card = 16 := by
    have hsizes := negative_sizeTwo_support_sizes (-5) Sp.card Sm.card
      hsupport.1 hsupport.2.1 (Or.inr (Or.inr rfl))
    rcases hsizes with h | h | h
    · omega
    · omega
    · exact h.2.2
  have hlevelOut : ∀ x, x ∉ c.supp → w x = -2 ∨ w x = 0 ∨ w x = 2 := by
    intro x _hx
    exact hthree.2.1 x
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
  have hO : O = Sp ∪ Sm ∪ Z0 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, O, Sp, Sm, Z0]
    constructor
    · intro hx
      rcases hlevelOut x hx with hm | hz | hp
      · exact Or.inl (Or.inr hm)
      · exact Or.inr ⟨hx, hz⟩
      · exact Or.inl (Or.inl hp)
    · rintro ((hp | hm) | hz)
      · exact hSpOut x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
      · exact hSmOut x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
      · exact hz.1
  have hdisjPS : Disjoint Sp Sm := by
    rw [Finset.disjoint_left]
    intro x hp hm
    have hp' := (Finset.mem_filter.mp hp).2
    have hm' := (Finset.mem_filter.mp hm).2
    omega
  have hdisjPZ : Disjoint Sp Z0 := by
    rw [Finset.disjoint_left]
    intro x hp hz
    have hp' := (Finset.mem_filter.mp hp).2
    have hz' := (Finset.mem_filter.mp hz).2.2
    omega
  have hdisjSZ : Disjoint Sm Z0 := by
    rw [Finset.disjoint_left]
    intro x hm hz
    have hm' := (Finset.mem_filter.mp hm).2
    have hz' := (Finset.mem_filter.mp hz).2.2
    omega
  have hOCard : O.card = 48 := by
    have hCcard : ((Finset.univ : Finset V).filter fun x => x ∈ c.supp).card = 16 := by
      let C := (Finset.univ : Finset V).filter fun x => x ∈ c.supp
      have hset : (↑C : Set V) = c.supp := by ext x; simp [C]
      calc
        C.card = (↑C : Set V).ncard := by simp
        _ = c.supp.ncard := congrArg Set.ncard hset
        _ = 16 := by norm_num at hc ⊢; exact hc
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset V)) (p := fun x => x ∈ c.supp)
    change _ + O.card = _ at hsplit
    rw [hCcard, Finset.card_univ, hcard] at hsplit
    omega
  have hZ0Card : Z0.card = 16 := by
    have hcardUnion : (Sp ∪ Sm ∪ Z0).card = Sp.card + Sm.card + Z0.card := by
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr ⟨hdisjPZ, hdisjSZ⟩),
        Finset.card_union_of_disjoint hdisjPS]
    rw [hO, hcardUnion, hSpCard, hSmCard] at hOCard
    omega
  have hS0Card : Fintype.card S0 = 16 := by
    let e : S0 ≃ {x : V // x ∈ Z0} :=
      Equiv.subtypeEquivRight fun x => by simp [S0, Z0, w, A]
    calc
      Fintype.card S0 = Fintype.card {x : V // x ∈ Z0} := Fintype.card_congr e
      _ = Z0.card := Fintype.card_coe Z0
      _ = 16 := hZ0Card
  have hcolumn (z : S0) :
      ((Finset.univ : Finset Xp).filter fun x => G.Adj x.1 z.1).card = 1 ∧
      ((Finset.univ : Finset Xm).filter fun x => G.Adj x.1 z.1).card = 1 := by
    let C := (G.neighborFinset z.1).filter
      (fun x => D.connectedComponentMk x = c)
    let Cp := C.filter fun x => s x = 1
    let Cm := C.filter fun x => s x = -1
    have hmem : ∀ x, x ∈ c.supp ↔ D.connectedComponentMk x = c :=
      fun x => ConnectedComponent.mem_supp_iff c x
    have hCcard : C.card = 2 := P.componentNeighborCard z.1
    have hcover : C = Cp ∪ Cm := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Cp, Cm]
      constructor
      · intro hx
        have hx' := Finset.mem_filter.mp (show x ∈ C from hx)
        have hxc : x ∈ c.supp := (hmem x).mpr hx'.2
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
    have hsumFull : ∑ x ∈ G.neighborFinset z.1, s x = 0 := by
      rw [← SimpleGraph.adjMatrix_mulVec_apply]
      have hzout : z.1 ∉ c.supp := z.2.1
      have hsz : s z.1 = 0 := hs_out z.1 hzout
      have hwz : A.mulVec s z.1 + 2 * s z.1 = 0 := z.2.2
      change A.mulVec s z.1 = 0
      omega
    have hsumC : ∑ x ∈ C, s x = 0 := by
      rw [← hsumFull]
      symm
      rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset z.1)
        (fun x => D.connectedComponentMk x = c)]
      have houtzero : ∑ x ∈ (G.neighborFinset z.1).filter
          (fun x => ¬D.connectedComponentMk x = c), s x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        apply hs_out x
        intro hxc
        exact (Finset.mem_filter.mp hx).2 ((hmem x).mp hxc)
      rw [houtzero, add_zero]
    have hsizes : Cp.card = 1 ∧ Cm.card = 1 := by
      have hsumSplit : (Cp.card : ℤ) - Cm.card = 0 := by
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
      omega
    have hXp : Finset.image Subtype.val
        ((Finset.univ : Finset Xp).filter fun x => G.Adj x.1 z.1) = Cp := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, Cp, C]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨(G.mem_neighborFinset _ _).mpr hy.symm,
          (hmem y.1).mp y.2.1⟩, y.2.2⟩
      · rintro ⟨⟨hxz, hxc⟩, hsx⟩
        refine ⟨⟨x, (hmem x).mpr hxc, hsx⟩,
          ((G.mem_neighborFinset _ _).mp hxz).symm, rfl⟩
    have hXm : Finset.image Subtype.val
        ((Finset.univ : Finset Xm).filter fun x => G.Adj x.1 z.1) = Cm := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, Cm, C]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨(G.mem_neighborFinset _ _).mpr hy.symm,
          (hmem y.1).mp y.2.1⟩, y.2.2⟩
      · rintro ⟨⟨hxz, hxc⟩, hsx⟩
        refine ⟨⟨x, (hmem x).mpr hxc, hsx⟩,
          ((G.mem_neighborFinset _ _).mp hxz).symm, rfl⟩
    constructor
    · calc
        _ = (Finset.image Subtype.val
            ((Finset.univ : Finset Xp).filter fun x => G.Adj x.1 z.1)).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ = Cp.card := congrArg Finset.card hXp
        _ = 1 := hsizes.1
    · calc
        _ = (Finset.image Subtype.val
            ((Finset.univ : Finset Xm).filter fun x => G.Adj x.1 z.1)).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ = Cm.card := congrArg Finset.card hXm
        _ = 1 := hsizes.2
  exact ⟨hS0Card, fun z => (hcolumn z).1, fun z => (hcolumn z).2⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_neutralFiber_profile
