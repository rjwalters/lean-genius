import Proofs.Erdos85SizeTwoMuNegThreeCrossPermutationNormalForm

/-! # Ambient owners of the `mu = -3` cross complement -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A cross-shore nondefect pair has a unique ambient common neighbour. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_existsUnique_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (x : MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
    (y : MuNegThreeNegativeShore (secondOrderDefectGraph G) c s)
    (hxy : ¬ (secondOrderDefectGraph G).Adj x.1 y.1) :
    ∃! z, G.Adj x.1 z ∧ G.Adj y.1 z := by
  classical
  let common := G.neighborFinset x.1 ∩ G.neighborFinset y.1
  have hcard : common.card = 1 :=
    orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_common_card_one
      G hfree c s x y hxy
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  refine ⟨z, ?_, ?_⟩
  · have : z ∈ common := by simp [hz]
    simpa [common] using this
  · intro w hw
    have hwmem : w ∈ common := by simpa [common] using hw
    simpa [hz] using hwmem

/-- The ambient owner of a cross-shore pair lies outside the signed defect
component: either possible sign would make it a forbidden same-sign ambient
neighbour of one endpoint. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_owner_not_mem_support
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
    (x : MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
    (y : MuNegThreeNegativeShore (secondOrderDefectGraph G) c s)
    (z : V) (hz : G.Adj x.1 z ∧ G.Adj y.1 z) :
    z ∉ c.supp := by
  intro hzc
  let C := fun u ↦ (G.neighborFinset u).filter
    (fun v ↦ (secondOrderDefectGraph G).connectedComponentMk v = c)
  have hprofile := orderSixtyFour_sizeTwo_muNegThree_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hzcomp : (secondOrderDefectGraph G).connectedComponentMk z = c :=
    (ConnectedComponent.mem_supp_iff c z).mp hzc
  rcases hs_in z hzc with hsz | hsz
  · have hmem : z ∈ (C y.1).filter (fun v ↦ s v = -1) := by
      simp [C, hz.2, hzcomp, hsz]
    have hzero := ((hprofile.2.2 y.1 y.2.1).2 y.2.2).1
    rw [Finset.card_eq_zero.mp hzero] at hmem
    simp at hmem
  · have hmem : z ∈ (C x.1).filter (fun v ↦ s v = 1) := by
      simp [C, hz.1, hzcomp, hsz]
    have hzero := ((hprofile.2.2 x.1 x.2.1).1 x.2.2).1
    rw [Finset.card_eq_zero.mp hzero] at hmem
    simp at hmem

/-- Choosing a normal form for the three cross-complement matchings also
chooses their three unique ambient-owner maps. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_ownerNormalForm
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
    ∃ f : Xp ≃ Xm, ∃ σ τ : Equiv.Perm Xp, ∃ o₀ oσ oτ : Xp → V,
      (∀ x, σ x ≠ x) ∧ (∀ x, τ x ≠ x) ∧ (∀ x, σ x ≠ τ x) ∧
      (∀ x z, (G.Adj x.1 z ∧ G.Adj (f x).1 z) ↔ z = o₀ x) ∧
      (∀ x z, (G.Adj x.1 z ∧ G.Adj (f (σ x)).1 z) ↔ z = oσ x) ∧
      (∀ x z, (G.Adj x.1 z ∧ G.Adj (f (τ x)).1 z) ↔ z = oτ x) ∧
      (∀ x, o₀ x ∉ c.supp) ∧ (∀ x, oσ x ∉ c.supp) ∧
      ∀ x, oτ x ∉ c.supp := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  obtain ⟨f, σ, τ, hf, hσ, hτ, hσne, hτne, hστ⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_permutationNormalForm
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hu₀ (x : Xp) : ∃! z, G.Adj x.1 z ∧ G.Adj (f x).1 z :=
    orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_existsUnique_owner
      G hfree c s x (f x) (hf x)
  have huσ (x : Xp) : ∃! z, G.Adj x.1 z ∧ G.Adj (f (σ x)).1 z :=
    orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_existsUnique_owner
      G hfree c s x (f (σ x)) (hσ x)
  have huτ (x : Xp) : ∃! z, G.Adj x.1 z ∧ G.Adj (f (τ x)).1 z :=
    orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_existsUnique_owner
      G hfree c s x (f (τ x)) (hτ x)
  let o₀ : Xp → V := fun x => Classical.choose (hu₀ x).exists
  let oσ : Xp → V := fun x => Classical.choose (huσ x).exists
  let oτ : Xp → V := fun x => Classical.choose (huτ x).exists
  refine ⟨f, σ, τ, o₀, oσ, oτ, hσne, hτne, hστ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x z
    constructor
    · intro hz
      exact (hu₀ x).unique hz (Classical.choose_spec (hu₀ x).exists)
    · rintro rfl
      exact Classical.choose_spec (hu₀ x).exists
  · intro x z
    constructor
    · intro hz
      exact (huσ x).unique hz (Classical.choose_spec (huσ x).exists)
    · rintro rfl
      exact Classical.choose_spec (huσ x).exists
  · intro x z
    constructor
    · intro hz
      exact (huτ x).unique hz (Classical.choose_spec (huτ x).exists)
    · rintro rfl
      exact Classical.choose_spec (huτ x).exists
  · intro x
    exact orderSixtyFour_sizeTwo_muNegThree_cross_owner_not_mem_support
      G hfree hreg hcard c hc s hs_out hs_in hH hD x (f x) (o₀ x)
        (Classical.choose_spec (hu₀ x).exists)
  · intro x
    exact orderSixtyFour_sizeTwo_muNegThree_cross_owner_not_mem_support
      G hfree hreg hcard c hc s hs_out hs_in hH hD x (f (σ x)) (oσ x)
        (Classical.choose_spec (huσ x).exists)
  · intro x
    exact orderSixtyFour_sizeTwo_muNegThree_cross_owner_not_mem_support
      G hfree hreg hcard c hc s hs_out hs_in hH hD x (f (τ x)) (oτ x)
        (Classical.choose_spec (huτ x).exists)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_existsUnique_owner
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_owner_not_mem_support
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_ownerNormalForm
