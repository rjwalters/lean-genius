import Proofs.Erdos85ThreeLevelEigenSupportEdgeCensus
import Proofs.Erdos85GadgetDegreeSquares

/-! # C4-free degree-square bounds for the extreme fibres -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An induced subgraph of a C4-free graph is C4-free. -/
theorem not_containsC4_induce_finset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (S : Finset V) :
    ¬ containsC4 (↑S : Set V) (G.induce (↑S : Set V)) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  exact ⟨fun i ↦ (f i).1, Subtype.val_injective.comp hf,
    fun i j hij ↦ hadj i j hij⟩

/-- The local `+2` degree balance and C4-freeness bound the cross-incidence
count by the degree-square inequality on either extreme induced graph. -/
theorem extreme_support_cross_square_le_of_degreeBalance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (Sp Sm : Finset V) (hbal : Sp.card = Sm.card)
    (hp : ∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card + 2)
    (hm : ∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card + 2) :
    let cross := ∑ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card
    (cross + 2 * Sp.card) * (cross + 2 * Sp.card) ≤
      2 * Sp.card * Sp.card * (Sp.card - 1) := by
  dsimp only
  let cross := ∑ u ∈ Sp,
    ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card
  let H := G.induce (↑Sp : Set V)
  let ep := H.edgeFinset.card
  have hcensus := extreme_support_edgeCensus_of_degreeBalance
    G Sp Sm hbal hp hm
  change Even cross ∧ ep = _ ∧
    2 * ep = cross + 2 * Sp.card ∧ _ at hcensus
  have hhand := H.sum_degrees_eq_twice_card_edges
  have hsum : (∑ x : (↑Sp : Set V), H.degree x) =
      cross + 2 * Sp.card := by
    rw [hhand, hcensus.2.2.1]
  have hcauchy := sum_degrees_sq_le_card_mul_sum_degree_sq H
  have hsquares := sum_degree_sq_le_two_mul_card_mul_pred_of_not_containsC4
    H (not_containsC4_induce_finset G hfree Sp)
  have hcard : Fintype.card (↑Sp : Set V) = Sp.card := by
    simp
  calc
    (cross + 2 * Sp.card) * (cross + 2 * Sp.card) =
        (∑ x : (↑Sp : Set V), H.degree x) *
          (∑ x : (↑Sp : Set V), H.degree x) := by rw [hsum]
    _ ≤ Fintype.card (↑Sp : Set V) *
        ∑ x : (↑Sp : Set V), H.degree x * H.degree x := hcauchy
    _ ≤ Fintype.card (↑Sp : Set V) *
        (2 * (Fintype.card (↑Sp : Set V) *
          (Fintype.card (↑Sp : Set V) - 1))) :=
      Nat.mul_le_mul_left _ hsquares
    _ = 2 * Sp.card * Sp.card * (Sp.card - 1) := by
      rw [hcard]
      ring

/-- Arithmetic specialization: an eight-vertex extreme fibre has at most
twelve cross incidences and at most fourteen induced edges. -/
theorem extreme_support_eight_cross_le_twelve_edges_le_fourteen
    (cross ep : ℕ) (heven : Even cross)
    (hedges : 2 * ep = cross + 2 * 8)
    (hsquare : (cross + 2 * 8) * (cross + 2 * 8) ≤
      2 * 8 * 8 * (8 - 1)) :
    cross ≤ 12 ∧ ep ≤ 14 := by
  obtain ⟨k, hk⟩ := heven
  norm_num at hedges hsquare
  constructor
  · by_contra hnot
    have h14 : 14 ≤ cross := by omega
    nlinarith
  · have hcross : cross ≤ 12 := by
      by_contra hnot
      have h14 : 14 ≤ cross := by omega
      nlinarith
    omega

/-- Campaign-facing `μ = -1` specialization. -/
theorem orderSixtyFour_sizeTwo_muNegOne_extreme_cross_le_twelve_edges_le_fourteen
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
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = (-1 : ℤ) * s z) :
    let w := fun x ↦ (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x ↦ w x = 2
    let Sm := Finset.univ.filter fun x ↦ w x = -2
    let cross := ∑ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card
    let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
    cross ≤ 12 ∧ ep ≤ 14 := by
  dsimp only
  let w := fun x ↦ (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := Finset.univ.filter fun x ↦ w x = 2
  let Sm := Finset.univ.filter fun x ↦ w x = -2
  let cross := ∑ u ∈ Sp,
    ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card
  let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  change Sp.card = Sm.card ∧
    4 * (Sp.card : ℤ) = 8 * (3 - (-1 : ℤ)) ∧ _ at hprofile
  have hSpcard : Sp.card = 8 := by omega
  have hdeg := orderSixtyFour_sizeTwo_signedJoint_extreme_degreeBalance_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  change (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card + 2) at hdeg
  have hcensus := extreme_support_edgeCensus_of_degreeBalance
    G Sp Sm hprofile.1 hdeg.1 hdeg.2
  change Even cross ∧ ep = _ ∧
    2 * ep = cross + 2 * Sp.card ∧ _ at hcensus
  have hsquare := extreme_support_cross_square_le_of_degreeBalance
    G hfree Sp Sm hprofile.1 hdeg.1 hdeg.2
  change (cross + 2 * Sp.card) * (cross + 2 * Sp.card) ≤
    2 * Sp.card * Sp.card * (Sp.card - 1) at hsquare
  apply extreme_support_eight_cross_le_twelve_edges_le_fourteen
    cross ep hcensus.1
  · simpa [hSpcard] using hcensus.2.2.1
  · simpa [hSpcard] using hsquare

#print axioms Erdos85.extreme_support_cross_square_le_of_degreeBalance
#print axioms Erdos85.extreme_support_eight_cross_le_twelve_edges_le_fourteen
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_extreme_cross_le_twelve_edges_le_fourteen

end

end Erdos85
