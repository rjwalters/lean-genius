import Proofs.Erdos85SizeTwoMuNegFiveNeutralFiber

/-! # Biregular neutral incidence at `mu=-5` -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Every sign-shore vertex has exactly two neutral exterior neighbors.  In
combination with the neutral-fiber profile, the neutral incidence system has
row degree two and column degree one on each shore. -/
theorem orderSixtyFour_sizeTwo_muNegFive_neutralIncidence_biregular
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
    let R0p := fun x : Xp => fun z : S0 => G.Adj x.1 z.1
    let R0m := fun x : Xm => fun z : S0 => G.Adj x.1 z.1
    (∀ x, ((Finset.univ : Finset S0).filter fun z => R0p x z).card = 2) ∧
    (∀ z, ((Finset.univ : Finset Xp).filter fun x => R0p x z).card = 1) ∧
    (∀ x, ((Finset.univ : Finset S0).filter fun z => R0m x z).card = 2) ∧
    ∀ z, ((Finset.univ : Finset Xm).filter fun x => R0m x z).card = 1 := by
  classical
  dsimp only
  let A := G.adjMatrix ℤ
  let w : V → ℤ := fun x => A.mulVec s x + 2 * s x
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let S0 := MuNegFiveNeutralFiber G c s
  let R0p := fun x : Xp => fun z : S0 => G.Adj x.1 z.1
  let R0m := fun x : Xm => fun z : S0 => G.Adj x.1 z.1
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  have hthree := orderSixtyFour_sizeTwo_signedJoint_threeLevelAction_of_local
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  have hsat := orderSixtyFour_sizeTwo_muNegFive_extreme_rowSaturation_of_local
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hneutral := orderSixtyFour_sizeTwo_muNegFive_neutralFiber_profile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hrow (x : V) (hxc : x ∈ c.supp) (hsx : s x = 1 ∨ s x = -1) :
      ((G.neighborFinset x).filter
        fun z => z ∉ c.supp ∧ w z = 0).card = 2 := by
    let C := (G.neighborFinset x).filter
      (fun z => D.connectedComponentMk z = c)
    let O := (G.neighborFinset x).filter fun z => z ∉ c.supp
    let Np := O.filter fun z => w z = 2
    let Nm := O.filter fun z => w z = -2
    let N0 := (G.neighborFinset x).filter fun z => z ∉ c.supp ∧ w z = 0
    have hmem : ∀ z, z ∈ c.supp ↔ D.connectedComponentMk z = c :=
      fun z => ConnectedComponent.mem_supp_iff c z
    have hCcard : C.card = 2 := P.componentNeighborCard x
    have hdegree : (G.neighborFinset x).card = 8 := by
      rw [G.card_neighborFinset_eq_degree, hreg]
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := G.neighborFinset x) (p := fun z => z ∈ c.supp)
    have hCin : (G.neighborFinset x).filter (fun z => z ∈ c.supp) = C := by
      ext z
      simp [C, hmem]
    change ((G.neighborFinset x).filter fun z => z ∈ c.supp).card +
      O.card = (G.neighborFinset x).card at hsplit
    rw [hCin, hCcard, hdegree] at hsplit
    have hOcard : O.card = 6 := by omega
    have hOeq : O = Np ∪ Nm ∪ N0 := by
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, O, Np, Nm, N0]
      constructor
      · intro hz
        rcases hthree.2.1 z with hm | hzero | hp
        · exact Or.inl (Or.inr ⟨hz, hm⟩)
        · exact Or.inr ⟨hz.1, hz.2, hzero⟩
        · exact Or.inl (Or.inl ⟨hz, hp⟩)
      · rintro ((hp | hm) | hzero)
        · exact hp.1
        · exact hm.1
        · exact ⟨hzero.1, hzero.2.1⟩
    have hdisjPM : Disjoint Np Nm := by
      rw [Finset.disjoint_left]
      intro z hp hm
      have hp' := (Finset.mem_filter.mp hp).2
      have hm' := (Finset.mem_filter.mp hm).2
      omega
    have hdisjP0 : Disjoint Np N0 := by
      rw [Finset.disjoint_left]
      intro z hp hzero
      have hp' := (Finset.mem_filter.mp hp).2
      have hzero' := (Finset.mem_filter.mp hzero).2.2
      omega
    have hdisjM0 : Disjoint Nm N0 := by
      rw [Finset.disjoint_left]
      intro z hm hzero
      have hm' := (Finset.mem_filter.mp hm).2
      have hzero' := (Finset.mem_filter.mp hzero).2.2
      omega
    have hsumCard : O.card = Np.card + Nm.card + N0.card := by
      rw [hOeq, Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr ⟨hdisjP0, hdisjM0⟩),
        Finset.card_union_of_disjoint hdisjPM]
    change N0.card = 2
    rcases hsx with hsx | hsx
    · have hs := (hsat x hxc).1 hsx
      change Np.card = 4 ∧ Nm.card = 0 at hs
      rw [hOcard, hs.1, hs.2] at hsumCard
      omega
    · have hs := (hsat x hxc).2 hsx
      change Nm.card = 4 ∧ Np.card = 0 at hs
      rw [hOcard, hs.1, hs.2] at hsumCard
      omega
  have hrowP : ∀ x : Xp,
      ((Finset.univ : Finset S0).filter fun z => R0p x z).card = 2 := by
    intro x
    let N0 := (G.neighborFinset x.1).filter
      fun z => z ∉ c.supp ∧ w z = 0
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset S0).filter fun z => R0p x z) = N0 := by
      ext z
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, R0p, N0]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(G.mem_neighborFinset _ _).mpr hy,
          y.2.1, y.2.2⟩
      · rintro ⟨hzx, hzout, hwz⟩
        refine ⟨⟨z, hzout, hwz⟩,
          (G.mem_neighborFinset _ _).mp hzx, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset S0).filter fun z => R0p x z)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = N0.card := congrArg Finset.card himage
      _ = 2 := hrow x.1 x.2.1 (Or.inl x.2.2)
  have hrowM : ∀ x : Xm,
      ((Finset.univ : Finset S0).filter fun z => R0m x z).card = 2 := by
    intro x
    let N0 := (G.neighborFinset x.1).filter
      fun z => z ∉ c.supp ∧ w z = 0
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset S0).filter fun z => R0m x z) = N0 := by
      ext z
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, R0m, N0]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(G.mem_neighborFinset _ _).mpr hy,
          y.2.1, y.2.2⟩
      · rintro ⟨hzx, hzout, hwz⟩
        refine ⟨⟨z, hzout, hwz⟩,
          (G.mem_neighborFinset _ _).mp hzx, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset S0).filter fun z => R0m x z)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = N0.card := congrArg Finset.card himage
      _ = 2 := hrow x.1 x.2.1 (Or.inr x.2.2)
  exact ⟨hrowP, hneutral.2.1, hrowM, hneutral.2.2⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_neutralIncidence_biregular
