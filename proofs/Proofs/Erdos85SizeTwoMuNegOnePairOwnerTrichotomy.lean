import Proofs.Erdos85SizeTwoMuNegOneShoreEdgePartition

/-! # Exact owner trichotomy for same-sign pairs at `mu = -1` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A `C₄`-free graph has at most one common owner in an injectively embedded
owner type. -/
theorem muNegOne_existsUnique_common_owner_of_not_containsC4
    {V X : Type*} [Fintype V] [Fintype X]
    [DecidableEq V] [DecidableEq X]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (f : X → V) (hf : Function.Injective f)
    {x y : V} (hxy : x ≠ y) (z : X)
    (hz : G.Adj x (f z) ∧ G.Adj y (f z)) :
    ∃! w : X, G.Adj x (f w) ∧ G.Adj y (f w) := by
  refine ⟨z, hz, ?_⟩
  intro w hw
  apply hf
  exact Finset.card_le_one.mp
    (common_le_one_of_not_containsC4 hfree x y hxy) (f w)
    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hw.1,
      (G.mem_neighborFinset _ _).mpr hw.2⟩) (f z)
    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hz.1,
      (G.mem_neighborFinset _ _).mpr hz.2⟩)

/-- Every distinct same-sign pair is either a defect pair, has a unique
opposite-shore internal owner, or has a unique same-sign extreme owner. The
two owner alternatives cannot occur simultaneously. -/
theorem orderSixtyFour_sizeTwo_muNegOne_sameSign_pair_owner_trichotomy
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
    let Ep := MuNegOnePositiveExteriorFiber G s
    let Em := MuNegOneNegativeExteriorFiber G s
    ((∀ x y : Xp, x ≠ y →
        D.Adj x.1 y.1 ∨
        (¬ D.Adj x.1 y.1 ∧
          ((∃! z : Xm, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1) ∨
            (∃! z : Ep, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1)))) ∧
      (∀ x y : Xp, x ≠ y →
        ¬ ((∃ z : Xm, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1) ∧
          ∃ w : Ep, G.Adj x.1 w.1 ∧ G.Adj y.1 w.1))) ∧
    ((∀ x y : Xm, x ≠ y →
        D.Adj x.1 y.1 ∨
        (¬ D.Adj x.1 y.1 ∧
          ((∃! z : Xp, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1) ∨
            (∃! z : Em, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1)))) ∧
      (∀ x y : Xm, x ≠ y →
        ¬ ((∃ z : Xp, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1) ∧
          ∃ w : Em, G.Adj x.1 w.1 ∧ G.Adj y.1 w.1))) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegOnePositiveShore D c s
  let Xm := MuNegOneNegativeShore D c s
  let Ep := MuNegOnePositiveExteriorFiber G s
  let Em := MuNegOneNegativeExteriorFiber G s
  let B : Xp → Xm → Prop := fun x z ↦ G.Adj x.1 z.1
  let Rp : Xp → Ep → Prop := fun x z ↦ G.Adj x.1 z.1
  let Rm : Xm → Em → Prop := fun x z ↦ G.Adj x.1 z.1
  let Dp := D.comap (fun x : Xp ↦ x.1)
  let Dm := D.comap (fun x : Xm ↦ x.1)
  have hpart := orderSixtyFour_sizeTwo_muNegOne_shore_edge_partitions
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have howner := orderSixtyFour_sizeTwo_muNegOne_extremeOwner_profile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have no_mixed_p (x y : Xp) (hxy : x ≠ y) :
      ¬ ((∃ z : Xm, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1) ∧
        ∃ w : Ep, G.Adj x.1 w.1 ∧ G.Adj y.1 w.1) := by
    rintro ⟨⟨z, hxz, hyz⟩, w, hxw, hyw⟩
    have hxyval : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
    have heq : z.1 = w.1 := Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1 hxyval) z.1
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxz,
        (G.mem_neighborFinset _ _).mpr hyz⟩) w.1
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxw,
        (G.mem_neighborFinset _ _).mpr hyw⟩)
    exact (howner.2.2.1 w).1 (heq ▸ z.2.1)
  have no_mixed_m (x y : Xm) (hxy : x ≠ y) :
      ¬ ((∃ z : Xp, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1) ∧
        ∃ w : Em, G.Adj x.1 w.1 ∧ G.Adj y.1 w.1) := by
    rintro ⟨⟨z, hxz, hyz⟩, w, hxw, hyw⟩
    have hxyval : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
    have heq : z.1 = w.1 := Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1 hxyval) z.1
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxz,
        (G.mem_neighborFinset _ _).mpr hyz⟩) w.1
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxw,
        (G.mem_neighborFinset _ _).mpr hyw⟩)
    exact (howner.2.2.2 w).1 (heq ▸ z.2.1)
  constructor
  · constructor
    · intro x y hxy
      have hall : ((Dp ⊔ twoIncidenceShadow B) ⊔
          twoIncidenceShadow Rp).Adj x y := by
        rw [hpart.1]
        exact hxy
      rcases hall with (hdef | hint) | hext
      · exact Or.inl hdef
      · refine Or.inr ⟨?_, Or.inl ?_⟩
        · exact fun hd ↦ muNegOne_defect_comap_disjoint_twoIncidenceShadow
            G hfree Subtype.val Subtype.val_injective Subtype.val B
              (fun _ _ h ↦ h) hd hint
        · obtain ⟨-, z, hxz, hyz⟩ := hint
          exact muNegOne_existsUnique_common_owner_of_not_containsC4 G hfree
            Subtype.val Subtype.val_injective
            (fun h ↦ hxy (Subtype.ext h)) z ⟨hxz, hyz⟩
      · refine Or.inr ⟨?_, Or.inr ?_⟩
        · exact fun hd ↦ muNegOne_defect_comap_disjoint_twoIncidenceShadow
            G hfree Subtype.val Subtype.val_injective Subtype.val Rp
              (fun _ _ h ↦ h) hd hext
        · obtain ⟨-, z, hxz, hyz⟩ := hext
          exact muNegOne_existsUnique_common_owner_of_not_containsC4 G hfree
            Subtype.val Subtype.val_injective
            (fun h ↦ hxy (Subtype.ext h)) z ⟨hxz, hyz⟩
    · exact no_mixed_p
  · constructor
    · intro x y hxy
      have hall : ((Dm ⊔ twoIncidenceShadow (fun y x ↦ B x y)) ⊔
          twoIncidenceShadow Rm).Adj x y := by
        rw [hpart.2]
        exact hxy
      rcases hall with (hdef | hint) | hext
      · exact Or.inl hdef
      · refine Or.inr ⟨?_, Or.inl ?_⟩
        · exact fun hd ↦ muNegOne_defect_comap_disjoint_twoIncidenceShadow
            G hfree Subtype.val Subtype.val_injective Subtype.val
              (fun y x ↦ B x y) (fun _ _ h ↦ h.symm) hd hint
        · obtain ⟨-, z, hxz, hyz⟩ := hint
          exact muNegOne_existsUnique_common_owner_of_not_containsC4 G hfree
            Subtype.val Subtype.val_injective
            (fun h ↦ hxy (Subtype.ext h)) z ⟨hxz.symm, hyz.symm⟩
      · refine Or.inr ⟨?_, Or.inr ?_⟩
        · exact fun hd ↦ muNegOne_defect_comap_disjoint_twoIncidenceShadow
            G hfree Subtype.val Subtype.val_injective Subtype.val Rm
              (fun _ _ h ↦ h) hd hext
        · obtain ⟨-, z, hxz, hyz⟩ := hext
          exact muNegOne_existsUnique_common_owner_of_not_containsC4 G hfree
            Subtype.val Subtype.val_injective
            (fun h ↦ hxy (Subtype.ext h)) z ⟨hxz, hyz⟩
    · exact no_mixed_m

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_sameSign_pair_owner_trichotomy
