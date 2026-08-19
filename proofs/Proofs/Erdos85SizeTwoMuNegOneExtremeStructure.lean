import Proofs.Erdos85ThreeLevelEigenSupportC4Bound

/-! # Exact first reduction for the size-two `mu = -1` branch -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- The handshake identity and the C4 square bound leave exactly seven
possible cross/induced-edge census triples at extreme-fibre size eight. -/
theorem muNegOne_extreme_census_cases
    (cross ep em : Nat) (heven : Even cross) (hle : cross ≤ 12)
    (heq : ep = em) (hhand : 2 * ep = cross + 16) :
    (cross = 0 ∧ ep = 8 ∧ em = 8) ∨
    (cross = 2 ∧ ep = 9 ∧ em = 9) ∨
    (cross = 4 ∧ ep = 10 ∧ em = 10) ∨
    (cross = 6 ∧ ep = 11 ∧ em = 11) ∨
    (cross = 8 ∧ ep = 12 ∧ em = 12) ∨
    (cross = 10 ∧ ep = 13 ∧ em = 13) ∨
    (cross = 12 ∧ ep = 14 ∧ em = 14) := by
  obtain ⟨k, rfl⟩ := heven
  omega

/-- In the `mu = -1` joint-line branch the two extreme fibres both have
eight vertices and minimum internal degree two.  Their induced edge counts
agree, and their entire remaining census is one of seven explicit cases. -/
theorem orderSixtyFour_sizeTwo_muNegOne_extreme_structure
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
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-1 : ℤ) * s z) :
    let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x => w x = 2
    let Sm := Finset.univ.filter fun x => w x = -2
    let cross := ∑ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card
    let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
    let em := (G.induce (↑Sm : Set V)).edgeFinset.card
    Sp.card = 8 ∧ Sm.card = 8 ∧
    (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card) ∧
    ((cross = 0 ∧ ep = 8 ∧ em = 8) ∨
      (cross = 2 ∧ ep = 9 ∧ em = 9) ∨
      (cross = 4 ∧ ep = 10 ∧ em = 10) ∨
      (cross = 6 ∧ ep = 11 ∧ em = 11) ∨
      (cross = 8 ∧ ep = 12 ∧ em = 12) ∨
      (cross = 10 ∧ ep = 13 ∧ em = 13) ∨
      (cross = 12 ∧ ep = 14 ∧ em = 14)) := by
  dsimp only
  let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := Finset.univ.filter fun x => w x = 2
  let Sm := Finset.univ.filter fun x => w x = -2
  let cross := ∑ u ∈ Sp,
    ((G.neighborFinset u).filter fun y => y ∈ Sm).card
  let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
  let em := (G.induce (↑Sm : Set V)).edgeFinset.card
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  change Sp.card = Sm.card ∧
    4 * (Sp.card : ℤ) = 8 * (3 - (-1 : ℤ)) ∧
    (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card)
      at hprofile
  have hSp : Sp.card = 8 := by omega
  have hSm : Sm.card = 8 := by omega
  have hdeg := orderSixtyFour_sizeTwo_signedJoint_extreme_degreeBalance_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  change (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sp).card + 2) at hdeg
  have hcensus := extreme_support_edgeCensus_of_degreeBalance
    G Sp Sm hprofile.1 hdeg.1 hdeg.2
  change Even cross ∧ ep = em ∧
    2 * ep = cross + 2 * Sp.card ∧
    2 * em = cross + 2 * Sm.card at hcensus
  have hbound :=
    orderSixtyFour_sizeTwo_muNegOne_extreme_cross_le_twelve_edges_le_fourteen
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  change cross ≤ 12 ∧ ep ≤ 14 at hbound
  refine ⟨hSp, hSm, hprofile.2.2.1, hprofile.2.2.2, ?_⟩
  exact muNegOne_extreme_census_cases cross ep em hcensus.1 hbound.1
    hcensus.2.1 (by simpa [hSp] using hcensus.2.2.1)

end

end Erdos85

#print axioms Erdos85.muNegOne_extreme_census_cases
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_extreme_structure
