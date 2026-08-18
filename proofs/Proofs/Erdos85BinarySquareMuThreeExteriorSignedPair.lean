import Proofs.Erdos85BinarySquareSizeTwoMuThreeCollapse
import Proofs.Erdos85CrossEdgeTriangleDichotomy

/-!
# Explicit signed exterior pairs in the size-two `mu = 3` branch

The balanced-filter conclusion is converted into two actual component
neighbours, one of each sign, together with the exact-pair property required
by the exterior triangle dichotomy.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem orderSixtyFour_signedSizeTwo_muThree_exterior_signedPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2)
    (u : V) (hu : u ∉ c.supp) :
    ∃ z z' : V,
      G.Adj u z ∧ G.Adj u z' ∧ z ∈ c.supp ∧ z' ∈ c.supp ∧
      s z = 1 ∧ s z' = -1 ∧ z ≠ z' ∧
      ∀ y, G.Adj u y → y ∈ c.supp → y = z ∨ y = z' := by
  let T := (G.neighborFinset u).filter
    (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)
  have hbal := orderSixtyFour_signedSizeTwo_muThree_exterior_balancedPair
    G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out u hu
  change (T.filter fun y => s y = 1).card = 1 ∧
    (T.filter fun y => s y = -1).card = 1 at hbal
  obtain ⟨z, hzEq⟩ := Finset.card_eq_one.mp hbal.1
  obtain ⟨z', hz'Eq⟩ := Finset.card_eq_one.mp hbal.2
  have hzFilter : z ∈ T.filter (fun y => s y = 1) := by
    rw [hzEq]
    simp
  have hz'Filter : z' ∈ T.filter (fun y => s y = -1) := by
    rw [hz'Eq]
    simp
  have hzT := (Finset.mem_filter.mp hzFilter).1
  have hz'T := (Finset.mem_filter.mp hz'Filter).1
  have hsz : s z = 1 := (Finset.mem_filter.mp hzFilter).2
  have hsz' : s z' = -1 := (Finset.mem_filter.mp hz'Filter).2
  have huz : G.Adj u z :=
    (G.mem_neighborFinset u z).mp (Finset.mem_filter.mp hzT).1
  have huz' : G.Adj u z' :=
    (G.mem_neighborFinset u z').mp (Finset.mem_filter.mp hz'T).1
  have hzc : z ∈ c.supp := (ConnectedComponent.mem_supp_iff c z).mpr
    (Finset.mem_filter.mp hzT).2
  have hz'c : z' ∈ c.supp := (ConnectedComponent.mem_supp_iff c z').mpr
    (Finset.mem_filter.mp hz'T).2
  have hne : z ≠ z' := by
    intro h
    rw [h] at hsz
    omega
  refine ⟨z, z', huz, huz', hzc, hz'c, hsz, hsz', hne, ?_⟩
  intro y huy hyc
  have hyT : y ∈ T := Finset.mem_filter.mpr ⟨
    (G.mem_neighborFinset u y).mpr huy,
    (ConnectedComponent.mem_supp_iff c y).mp hyc⟩
  rcases hs_in y hyc with hsy | hsy
  · right
    have : y ∈ T.filter (fun a => s a = -1) := Finset.mem_filter.mpr ⟨hyT, hsy⟩
    rw [hz'Eq] at this
    simpa using this
  · left
    have : y ∈ T.filter (fun a => s a = 1) := Finset.mem_filter.mpr ⟨hyT, hsy⟩
    rw [hzEq] at this
    simpa using this

/-- The explicit signed pair is immediately compatible with the exterior
triangle dichotomy. -/
theorem orderSixtyFour_signedSizeTwo_muThree_exterior_signedPair_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2)
    (u : V) (hu : u ∉ c.supp) :
    ∃ z z' : V,
      s z = 1 ∧ s z' = -1 ∧ z ∈ c.supp ∧ z' ∈ c.supp ∧ z ≠ z' ∧
      ((G.Adj z z' → ∀ y, G.Adj u y → y ∉ c.supp →
          ¬ G.Adj z y ∧ ¬ G.Adj z' y) ∧
       (¬ G.Adj z z' →
          (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z y) ∧
          (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z' y))) := by
  obtain ⟨z, z', huz, huz', hzc, hz'c, hsz, hsz', hne, hpair⟩ :=
    orderSixtyFour_signedSizeTwo_muThree_exterior_signedPair
      G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out u hu
  exact ⟨z, z', hsz, hsz', hzc, hz'c, hne,
    exterior_triangle_dichotomy G hfree c hu hzc hz'c hne huz huz' hpair⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_signedSizeTwo_muThree_exterior_signedPair
#print axioms Erdos85.orderSixtyFour_signedSizeTwo_muThree_exterior_signedPair_dichotomy
