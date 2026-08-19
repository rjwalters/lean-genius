import Proofs.Erdos85SizeTwoMuNegFiveSignedStructure
import Proofs.Erdos85OneRegularRelationEquiv

/-!
# Matching normalization at defect eigenvalue `-5`

The signed degree profile gives every vertex exactly one same-sign defect
neighbour.  Symmetry and irreflexivity therefore turn the two same-sign
relations into fixed-point-free involutions: one perfect matching on each
eight-vertex shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

abbrev MuNegFivePositiveShore {V : Type*}
    (D : SimpleGraph V) (c : D.ConnectedComponent) (s : V → ℤ) :=
  {x : V // x ∈ c.supp ∧ s x = 1}

abbrev MuNegFiveNegativeShore {V : Type*}
    (D : SimpleGraph V) (c : D.ConnectedComponent) (s : V → ℤ) :=
  {x : V // x ∈ c.supp ∧ s x = -1}

/-- A symmetric irreflexive one-regular relation is a perfect matching,
presented as a fixed-point-free involutive permutation. -/
theorem symmetric_irreflexive_oneRegularRelation_exists_matching
    {X : Type*} [Fintype X] [DecidableEq X]
    (R : X → X → Prop) [DecidableRel R]
    (hR : RelationOneRegular R)
    (hsymm : ∀ {x y}, R x y → R y x)
    (hirr : ∀ x, ¬ R x x) :
    ∃ f : Equiv.Perm X,
      (∀ x y, R x y ↔ f x = y) ∧
      (∀ x, f (f x) = x) ∧
      (∀ x, f x ≠ x) := by
  obtain ⟨f, hf⟩ := oneRegularRelation_exists_equiv R hR
  have hedge (x : X) : R x (f x) := (hf x (f x)).mpr rfl
  refine ⟨f, hf, ?_, ?_⟩
  · intro x
    exact (hf (f x) x).mp (hsymm (hedge x))
  · intro x hfix
    exact hirr x ((hf x x).mpr hfix)

/-- At `mu=-5`, same-sign defect adjacency on each eight-vertex shore is a
perfect matching. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sameSign_defect_matchings
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
    ∃ fp : Equiv.Perm Xp, ∃ fm : Equiv.Perm Xm,
      (∀ x y, D.Adj x.1 y.1 ↔ fp x = y) ∧
      (∀ x, fp (fp x) = x) ∧ (∀ x, fp x ≠ x) ∧
      (∀ x y, D.Adj x.1 y.1 ↔ fm x = y) ∧
      (∀ x, fm (fm x) = x) ∧ (∀ x, fm x ≠ x) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  have hprofile := orderSixtyFour_sizeTwo_muNegFive_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hsamePos (x : Xp) :
      ((Finset.univ : Finset Xp).filter fun y => D.Adj x.1 y.1).card = 1 := by
    have himage :
        Finset.image Subtype.val
            ((Finset.univ : Finset Xp).filter fun y => D.Adj x.1 y.1) =
          (D.neighborFinset x.1).filter fun y => s y = 1 := by
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
          ((Finset.univ : Finset Xp).filter fun y => D.Adj x.1 y.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = ((D.neighborFinset x.1).filter fun y => s y = 1).card :=
        congrArg Finset.card himage
      _ = 1 := (hprofile.2.2 x.1 x.2.1).1 x.2.2 |>.2.2.1
  have hsameNeg (x : Xm) :
      ((Finset.univ : Finset Xm).filter fun y => D.Adj x.1 y.1).card = 1 := by
    have himage :
        Finset.image Subtype.val
            ((Finset.univ : Finset Xm).filter fun y => D.Adj x.1 y.1) =
          (D.neighborFinset x.1).filter fun y => s y = -1 := by
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
          ((Finset.univ : Finset Xm).filter fun y => D.Adj x.1 y.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = ((D.neighborFinset x.1).filter fun y => s y = -1).card :=
        congrArg Finset.card himage
      _ = 1 := (hprofile.2.2 x.1 x.2.1).2 x.2.2 |>.2.2.1
  have hRpos : RelationOneRegular (fun x y : Xp => D.Adj x.1 y.1) := by
    refine ⟨hsamePos, ?_⟩
    intro y
    simpa only [D.adj_comm] using hsamePos y
  have hRneg : RelationOneRegular (fun x y : Xm => D.Adj x.1 y.1) := by
    refine ⟨hsameNeg, ?_⟩
    intro y
    simpa only [D.adj_comm] using hsameNeg y
  obtain ⟨fp, hfp, hfpinv, hfpne⟩ :=
    symmetric_irreflexive_oneRegularRelation_exists_matching
      (fun x y : Xp => D.Adj x.1 y.1) hRpos
      (fun h => h.symm) (fun x => D.loopless.irrefl x.1)
  obtain ⟨fm, hfm, hfminv, hfmne⟩ :=
    symmetric_irreflexive_oneRegularRelation_exists_matching
      (fun x y : Xm => D.Adj x.1 y.1) hRneg
      (fun h => h.symm) (fun x => D.loopless.irrefl x.1)
  exact ⟨fp, fm, hfp, hfpinv, hfpne, hfm, hfminv, hfmne⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sameSign_defect_matchings
