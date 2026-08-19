import Proofs.Erdos85ThreeLevelEigenSupportC4Bound

/-!
# The exact exterior normal form for the size-two `mu = -3` mode

The derived three-level vector has two twelve-vertex extreme fibres.  Its
same-sign degree exceeds its opposite-sign degree by two at every extreme
vertex.  Double counting and the induced `C4` bound then give equal induced
edge counts, an even cross count, and the numerical bounds used by the
remaining finite classification.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The numerical consequence of the degree-square inequality on a
twelve-vertex extreme fibre. -/
theorem extreme_support_twelve_cross_le_thirtyTwo_edges_le_twentyEight
    (cross ep : ℕ) (heven : Even cross)
    (hedges : 2 * ep = cross + 2 * 12)
    (hsquare : (cross + 2 * 12) * (cross + 2 * 12) ≤
      2 * 12 * 12 * (12 - 1)) :
    cross ≤ 32 ∧ ep ≤ 28 := by
  obtain ⟨k, hk⟩ := heven
  norm_num at hedges hsquare
  constructor
  · by_contra hnot
    have h34 : 34 ≤ cross := by omega
    nlinarith
  · have hcross : cross ≤ 32 := by
      by_contra hnot
      have h34 : 34 ≤ cross := by omega
      nlinarith
    omega

/-- Campaign-facing normal form for `mu = -3`.  Besides the exact `12+12`
support split, this records the vertexwise degree balance and the complete
edge/cross census, including the strongest immediate `C4` numerical bound. -/
theorem orderSixtyFour_sizeTwo_muNegThree_extreme_support_normalForm
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
    let w := fun x ↦ (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x ↦ w x = 2
    let Sm := Finset.univ.filter fun x ↦ w x = -2
    let cross := ∑ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card
    let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
    let em := (G.induce (↑Sm : Set V)).edgeFinset.card
    Sp.card = 12 ∧ Sm.card = 12 ∧
    (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card + 2) ∧
    Even cross ∧ ep = em ∧
    2 * ep = cross + 24 ∧ 2 * em = cross + 24 ∧
    cross ≤ 32 ∧ ep ≤ 28 := by
  dsimp only
  let w := fun x ↦ (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := Finset.univ.filter fun x ↦ w x = 2
  let Sm := Finset.univ.filter fun x ↦ w x = -2
  let cross := ∑ u ∈ Sp,
    ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card
  let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
  let em := (G.induce (↑Sm : Set V)).edgeFinset.card
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s (-3) hs_out hs_in hH hD
  change Sp.card = Sm.card ∧
    4 * (Sp.card : ℤ) = 8 * (3 - (-3 : ℤ)) ∧ _ at hprofile
  have hSp : Sp.card = 12 := by omega
  have hSm : Sm.card = 12 := by omega
  have hdeg := orderSixtyFour_sizeTwo_signedJoint_extreme_degreeBalance_of_local
    G hfree hreg hcard c hc s (-3) hs_out hs_in hH hD
  change (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card + 2) at hdeg
  have hcensus := extreme_support_edgeCensus_of_degreeBalance
    G Sp Sm hprofile.1 hdeg.1 hdeg.2
  change Even cross ∧ ep = em ∧
    2 * ep = cross + 2 * Sp.card ∧
    2 * em = cross + 2 * Sm.card at hcensus
  have hsquare := extreme_support_cross_square_le_of_degreeBalance
    G hfree Sp Sm hprofile.1 hdeg.1 hdeg.2
  change (cross + 2 * Sp.card) * (cross + 2 * Sp.card) ≤
    2 * Sp.card * Sp.card * (Sp.card - 1) at hsquare
  have hbound :=
    extreme_support_twelve_cross_le_thirtyTwo_edges_le_twentyEight
      cross ep hcensus.1 (by simpa [hSp] using hcensus.2.2.1)
        (by simpa [hSp] using hsquare)
  change Sp.card = 12 ∧ Sm.card = 12 ∧
    (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card + 2) ∧
    Even cross ∧ ep = em ∧
    2 * ep = cross + 24 ∧ 2 * em = cross + 24 ∧
    cross ≤ 32 ∧ ep ≤ 28
  exact ⟨hSp, hSm, hdeg.1, hdeg.2, hcensus.1, hcensus.2.1,
    by omega, by omega, hbound⟩

end

end Erdos85

#print axioms Erdos85.extreme_support_twelve_cross_le_thirtyTwo_edges_le_twentyEight
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_extreme_support_normalForm
