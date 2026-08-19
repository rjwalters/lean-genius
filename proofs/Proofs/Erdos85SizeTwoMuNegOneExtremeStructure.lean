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

/-- A C4-free graph on eight vertices with minimum degree at least two has
an actual degree-two vertex. -/
theorem exists_degree_eq_two_of_card_eight_of_c4Free
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcard : Fintype.card W = 8) (hfree : ¬ containsC4 W H)
    (hmin : ∀ x, 2 ≤ H.degree x) : ∃ x, H.degree x = 2 := by
  by_contra hnone
  push Not at hnone
  have hthree : ∀ x, 3 ≤ H.degree x := by
    intro x
    have := hmin x
    have := hnone x
    omega
  let e : W ≃ Fin 8 := Fintype.equivOfCardEq hcard
  let R : SimpleGraph (Fin 8) := SimpleGraph.comap e.symm H
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  have hRdegree : ∀ i, R.degree i = H.degree (e.symm i) := by
    intro i
    exact (SimpleGraph.Iso.comap e.symm H).degree_eq i |>.symm
  have hRmin : 3 ≤ R.minDegree := by
    apply R.le_minDegree_of_forall_le_degree
    intro i
    rw [hRdegree]
    exact hthree _
  have hRfour := containsC4_of_eight_min_degree_three R hRmin
  exact hfree ((containsC4_iff_of_iso
    (SimpleGraph.Iso.comap e.symm H)).mp hRfour)

theorem degree_induce_finset_eq_internalNeighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (x : (↑S : Set V)) :
    (G.induce (↑S : Set V)).degree x =
      ((G.neighborFinset x.1).filter fun y => y ∈ S).card := by
  rw [← (G.induce (↑S : Set V)).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    have hadj :=
      ((G.induce (↑S : Set V)).mem_neighborFinset x y).mp hy
    change G.Adj x.1 y.1 at hadj
    apply Finset.mem_filter.mpr
    exact ⟨(G.mem_neighborFinset x.1 y.1).mpr hadj,
      Finset.mem_coe.mp y.2⟩
  · intro y₁ _ y₂ _ hy
    exact Subtype.ext hy
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    refine ⟨⟨y, Finset.mem_coe.mpr hy'.2⟩, ?_, rfl⟩
    exact ((G.induce (↑S : Set V)).mem_neighborFinset x _).mpr
      ((G.mem_neighborFinset x.1 y).mp hy'.1)

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

/-- Each `mu = -1` extreme shore contains a degree-two vertex with no edge
to the opposite extreme shore. -/
theorem orderSixtyFour_sizeTwo_muNegOne_exists_cross_isolated_extremes
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
    (∃ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card = 2 ∧
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card = 0) ∧
    ∃ v ∈ Sm,
      ((G.neighborFinset v).filter fun y => y ∈ Sm).card = 2 ∧
      ((G.neighborFinset v).filter fun y => y ∈ Sp).card = 0 := by
  dsimp only
  let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := Finset.univ.filter fun x => w x = 2
  let Sm := Finset.univ.filter fun x => w x = -2
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
  let Hp := G.induce (↑Sp : Set V)
  let Hm := G.induce (↑Sm : Set V)
  have hpcard : Fintype.card (↑Sp : Set V) = 8 := by simp [hSp]
  have hmcard : Fintype.card (↑Sm : Set V) = 8 := by simp [hSm]
  have hpmin : ∀ x : (↑Sp : Set V), 2 ≤ Hp.degree x := by
    intro x
    rw [show Hp.degree x =
      ((G.neighborFinset x.1).filter fun y => y ∈ Sp).card by
        exact degree_induce_finset_eq_internalNeighbor_card G Sp x]
    exact hprofile.2.2.1 x.1 x.2
  have hmmin : ∀ x : (↑Sm : Set V), 2 ≤ Hm.degree x := by
    intro x
    rw [show Hm.degree x =
      ((G.neighborFinset x.1).filter fun y => y ∈ Sm).card by
        exact degree_induce_finset_eq_internalNeighbor_card G Sm x]
    exact hprofile.2.2.2 x.1 x.2
  obtain ⟨u, hu2⟩ := exists_degree_eq_two_of_card_eight_of_c4Free
    Hp hpcard (not_containsC4_induce_finset G hfree Sp) hpmin
  obtain ⟨v, hv2⟩ := exists_degree_eq_two_of_card_eight_of_c4Free
    Hm hmcard (not_containsC4_induce_finset G hfree Sm) hmmin
  have huInternal :
      ((G.neighborFinset u.1).filter fun y => y ∈ Sp).card = 2 := by
    rw [← degree_induce_finset_eq_internalNeighbor_card G Sp u]
    exact hu2
  have hvInternal :
      ((G.neighborFinset v.1).filter fun y => y ∈ Sm).card = 2 := by
    rw [← degree_induce_finset_eq_internalNeighbor_card G Sm v]
    exact hv2
  refine ⟨⟨u.1, u.2, huInternal, ?_⟩,
    ⟨v.1, v.2, hvInternal, ?_⟩⟩
  · have hz :
        ((G.neighborFinset u.1).filter fun y => y ∈ Sm).card + 2 = 2 :=
      (hdeg.1 u.1 u.2).symm.trans huInternal
    have hz0 : ((G.neighborFinset u.1).filter fun y => y ∈ Sm).card = 0 := by
      omega
    simpa [Sm, w] using hz0
  · have hz :
        ((G.neighborFinset v.1).filter fun y => y ∈ Sp).card + 2 = 2 :=
      (hdeg.2 v.1 v.2).symm.trans hvInternal
    have hz0 : ((G.neighborFinset v.1).filter fun y => y ∈ Sp).card = 0 := by
      omega
    simpa [Sp, w] using hz0

end

end Erdos85

#print axioms Erdos85.muNegOne_extreme_census_cases
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_extreme_structure
#print axioms Erdos85.exists_degree_eq_two_of_card_eight_of_c4Free
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_exists_cross_isolated_extremes
