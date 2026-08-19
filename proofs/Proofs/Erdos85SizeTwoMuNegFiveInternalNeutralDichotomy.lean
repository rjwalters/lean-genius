import Proofs.Erdos85SizeTwoMuNegFiveNeutralDefectComplement

/-! # Internal-versus-neutral dichotomy at `mu=-5` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At each positive-shore vertex, either its two internal ambient neighbors
are exactly its two neutral-projection partners, or the two rows are
disjoint.  The alternatives are detected by triangle-free degree zero or
two, respectively. -/
theorem orderSixtyFour_sizeTwo_muNegFive_internal_neutral_row_dichotomy
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
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
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
    let N := MuNegFiveNeutralProjection G c s
    ∀ x : Xp,
      ((triangleFreeEdgeGraph G).degree x.1 = 0 ∧
        ∀ y, B x y ↔ N x y) ∨
      ((triangleFreeEdgeGraph G).degree x.1 = 2 ∧
        ∀ y, B x y → ¬ N x y) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
  let N := MuNegFiveNeutralProjection G c s
  have hNregular :=
    orderSixtyFour_sizeTwo_muNegFive_neutralProjection_biregular
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hNiff :=
    orderSixtyFour_sizeTwo_muNegFive_neutralProjection_iff_not_defect
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  have hprofile := orderSixtyFour_sizeTwo_muNegFive_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hmem : ∀ y, y ∈ c.supp ↔ D.connectedComponentMk y = c :=
    fun y => ConnectedComponent.mem_supp_iff c y
  have hBrow : ∀ x : Xp,
      ((Finset.univ : Finset Xm).filter fun y => B x y).card = 2 := by
    intro x
    let C := (G.neighborFinset x.1).filter
      (fun y => D.connectedComponentMk y = c)
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset Xm).filter fun y => B x y) = C := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, B, C]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(G.mem_neighborFinset _ _).mpr hz, (hmem z.1).mp z.2.1⟩
      · rintro ⟨hxy, hyc⟩
        have hySupp := (hmem y).mpr hyc
        have hsy : s y = -1 := by
          rcases hs_in y hySupp with hsy | hsy
          · exact hsy
          · -- The signed internal profile rules out a positive ambient neighbor.
            have hzero := ((hprofile.2.2 x.1 x.2.1).1 x.2.2).1
            let Cp := C.filter fun z => s z = 1
            have hyC : y ∈ C := Finset.mem_filter.mpr ⟨hxy, hyc⟩
            have hymem : y ∈ Cp := Finset.mem_filter.mpr ⟨hyC, hsy⟩
            have : 0 < Cp.card := Finset.card_pos.mpr ⟨y, hymem⟩
            change Cp.card = 0 at hzero
            omega
        exact ⟨⟨y, hySupp, hsy⟩, (G.mem_neighborFinset _ _).mp hxy, rfl⟩
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Xm).filter fun y => B x y)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = C.card := congrArg Finset.card himage
      _ = 2 := P.componentNeighborCard x.1
  intro x
  rcases binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree (q := 8) (by omega) (by decide) hreg hcard c hc
      ⟨x.1, x.2.1⟩ with hzero | htwo
  · left
    have hzero' : (triangleFreeEdgeGraph G).degree x.1 = 0 := by simpa using hzero
    refine ⟨hzero', ?_⟩
    let BR := (Finset.univ : Finset Xm).filter fun y => B x y
    let NR := (Finset.univ : Finset Xm).filter fun y => N x y
    have hsub : BR ⊆ NR := by
      intro y hy
      have hBxy := (Finset.mem_filter.mp hy).2
      have hnotD : ¬ D.Adj x.1 y.1 := by
        intro hDxy
        change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x.1 y.1 at hDxy
        rcases hDxy with hanti | htf
        · exact ((mem_antipodalNeighbors G x.1 y.1).mp hanti).2.1 hBxy
        · have hymem : y.1 ∈ (triangleFreeEdgeGraph G).neighborFinset x.1 :=
            ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf
          have hpos : 0 < (triangleFreeEdgeGraph G).degree x.1 := by
            rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
            exact Finset.card_pos.mpr ⟨y.1, hymem⟩
          omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hNiff x y).2 hnotD⟩
    have heq : BR = NR := Finset.eq_of_subset_of_card_le hsub (by
      rw [hBrow x, hNregular.1 x])
    intro y
    constructor
    · intro hxy
      have : y ∈ BR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
      exact (Finset.mem_filter.mp (by rw [← heq]; exact this : y ∈ NR)).2
    · intro hxy
      have : y ∈ NR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
      exact (Finset.mem_filter.mp (by rw [heq]; exact this : y ∈ BR)).2
  · right
    have htwo' : (triangleFreeEdgeGraph G).degree x.1 = 2 := by simpa using htwo
    refine ⟨htwo', ?_⟩
    have hsubset := triangleFreeNeighbors_subset_componentNeighborFinset
      G c x.2.1
    have htfcard : (triangleFreeNeighbors G x.1).card = 2 := by
      calc
        _ = ((triangleFreeEdgeGraph G).neighborFinset x.1).card :=
          congrArg Finset.card (triangleFreeEdgeGraph_neighborFinset G x.1).symm
        _ = (triangleFreeEdgeGraph G).degree x.1 :=
          (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree x.1
        _ = 2 := htwo'
    have hcompcard :
        (componentNeighborFinset G D c x.1).card = 2 := P.componentNeighborCard x.1
    have heq : triangleFreeNeighbors G x.1 =
        componentNeighborFinset G D c x.1 :=
      Finset.eq_of_subset_of_card_le hsubset (by omega)
    intro y hBxy hNxy
    have hyComp : y.1 ∈ componentNeighborFinset G D c x.1 := by
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hBxy, (hmem y.1).mp y.2.1⟩
    have hyTf : y.1 ∈ triangleFreeNeighbors G x.1 := heq ▸ hyComp
    have hDxy : D.Adj x.1 y.1 := by
      change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x.1 y.1
      exact Or.inr ((triangleFreeEdgeGraph_adj G x.1 y.1).mpr hyTf)
    exact (hNiff x y).1 hNxy hDxy

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_internal_neutral_row_dichotomy
