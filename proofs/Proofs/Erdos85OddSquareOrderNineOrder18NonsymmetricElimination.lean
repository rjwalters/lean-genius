import Proofs.Erdos85OddSquareOrderNineOrder18SpikeReduction

/-!
# The nonsymmetric order-eighteen articulation branch

This file formalizes audit equations (16)--(18) for the six permutations of
the order-eighteen high-boundary profile `(1,2,3)`.  It is kept separate from
the symmetric spike reduction so the two articulation branches can be wired
independently.
-/

open scoped BigOperators

namespace Erdos85

open Finset SimpleGraph

/-- Equation (16) implies equation (17).  The two signed high-root correction
terms pass through the adjacency operator with the opposite signs. -/
theorem orderNine_order18_nonsymmetric_defect_equation_of_global_shore_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (H S Z : Finset V) (hminus hplus : V)
    (hHcard : H.card = 3) (hScard : S.card = 18)
    (hSH : Disjoint S H)
    (hdegOrd : ∀ x ∉ H, G.degree x = 9)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hdefectHighIsolated : ∀ h ∈ H,
      (secondOrderDefectGraph G).neighborFinset h = ∅)
    (hglobal : ∀ x : V,
      ((G.neighborFinset x ∩ S).card : ℤ) =
        2 + (if x ∈ Z then 1 else 0) -
          ((G.neighborFinset x ∩ H).card : ℤ) -
          (if x = hminus then 1 else 0) +
          (if x = hplus then 1 else 0)) :
    ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ S).card : ℤ) =
        8 * (if x ∈ S then 1 else 0) + 3 +
          7 * (if x ∈ H then 1 else 0) -
          ((G.neighborFinset x ∩ Z).card : ℤ) +
          (if G.Adj x hminus then 1 else 0) -
          (if G.Adj x hplus then 1 else 0) := by
  classical
  let D := secondOrderDefectGraph G
  intro x
  have hDHzero : (D.neighborFinset x ∩ H).card = 0 := by
    rw [Finset.card_eq_zero]
    ext y
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hyD hyH
    have hxy : D.Adj x y := (D.mem_neighborFinset x y).mp hyD
    have hyx : x ∈ D.neighborFinset y :=
      (D.mem_neighborFinset y x).mpr ((D.adj_comm x y).mp hxy)
    rw [hdefectHighIsolated y hyH] at hyx
    simp at hyx
  have htransferH := c4Free_secondOrderDefect_neighbor_inter_card_eq
    G hfree H x
  rw [hDHzero, hHcard] at htransferH
  have hsumH :
      (∑ y ∈ G.neighborFinset x,
        ((G.neighborFinset y ∩ H).card : ℤ)) =
      ((G.degree x : ℤ) - 1) * (if x ∈ H then 1 else 0) + 3 := by
    omega
  have hsumGlobal :
      (∑ y ∈ G.neighborFinset x,
        ((G.neighborFinset y ∩ S).card : ℤ)) =
      2 * (G.degree x : ℤ) +
        ((G.neighborFinset x ∩ Z).card : ℤ) -
        (∑ y ∈ G.neighborFinset x,
          ((G.neighborFinset y ∩ H).card : ℤ)) -
        (if G.Adj x hminus then 1 else 0) +
        (if G.Adj x hplus then 1 else 0) := by
    calc
      (∑ y ∈ G.neighborFinset x,
        ((G.neighborFinset y ∩ S).card : ℤ)) =
          ∑ y ∈ G.neighborFinset x,
            (2 + (if y ∈ Z then 1 else 0) -
              ((G.neighborFinset y ∩ H).card : ℤ) -
              (if y = hminus then 1 else 0) +
              (if y = hplus then 1 else 0)) := by
                apply Finset.sum_congr rfl
                intro y _
                exact hglobal y
      _ = 2 * (G.degree x : ℤ) +
          ((G.neighborFinset x ∩ Z).card : ℤ) -
          (∑ y ∈ G.neighborFinset x,
            ((G.neighborFinset y ∩ H).card : ℤ)) -
          (if G.Adj x hminus then 1 else 0) +
          (if G.Adj x hplus then 1 else 0) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              G.card_neighborFinset_eq_degree, G.mem_neighborFinset,
              mul_comm]
  have htransferS := c4Free_secondOrderDefect_neighbor_inter_card_eq
    G hfree S x
  rw [hScard, hsumGlobal, hsumH] at htransferS
  by_cases hxH : x ∈ H
  · have hxS : x ∉ S := fun hxS ↦ Finset.disjoint_left.mp hSH hxS hxH
    rw [hdegHigh x hxH] at htransferS
    simp [hxH, hxS] at htransferS ⊢
    ring_nf at htransferS ⊢
    exact htransferS
  · rw [hdegOrd x hxH] at htransferS
    simp [hxH] at htransferS ⊢
    ring_nf at htransferS ⊢
    exact htransferS

/-- Equations (17)--(18) contradict the three distinct original bin-one
partners.  At each high root equation (17) forces all ten neighbors into
`Z`; at the owner it forces `Z`-degree one, while the three partners give
three distinct owner-neighbors in `Z`. -/
theorem false_of_orderNine_order18_nonsymmetric_defect_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (H S Z partners : Finset V) (owner hminus hplus : V)
    (hSH : Disjoint S H)
    (hownerS : owner ∉ S) (hownerH : owner ∉ H)
    (hminusH : hminus ∈ H) (hplusH : hplus ∈ H)
    (hhighIndependent : ∀ h ∈ H, Disjoint (G.neighborFinset h) H)
    (hdegHigh : ∀ h ∈ H, G.degree h = 10)
    (hDhigh : ∀ h ∈ H, D.neighborFinset h = ∅)
    (hownerMinus : G.Adj owner hminus)
    (hownerPlus : G.Adj owner hplus)
    (hownerDefect : (D.neighborFinset owner ∩ S).card = 2)
    (heq17 : ∀ x : V,
      ((D.neighborFinset x ∩ S).card : ℤ) =
        8 * (if x ∈ S then 1 else 0) + 3 +
          7 * (if x ∈ H then 1 else 0) -
          ((G.neighborFinset x ∩ Z).card : ℤ) +
          (if G.Adj x hminus then 1 else 0) -
          (if G.Adj x hplus then 1 else 0))
    (hpartnerCard : partners.card = 3)
    (hpartnersOwner : partners ⊆ G.neighborFinset owner)
    (hpartnersRoot : ∀ p ∈ partners, ∃ h ∈ H, G.Adj h p) : False := by
  classical
  have hrootSaturation : ∀ h ∈ H, G.neighborFinset h ⊆ Z := by
    intro h hhH
    have hhS : h ∉ S := fun hhS ↦
      Finset.disjoint_left.mp hSH hhS hhH
    have hDzero : (D.neighborFinset h ∩ S).card = 0 := by
      rw [hDhigh h hhH]
      simp
    have heq := heq17 h
    rw [hDzero]
      at heq
    have hminusNotAdj : ¬ G.Adj h hminus := by
      intro hadj
      exact Finset.disjoint_left.mp (hhighIndependent h hhH)
        ((G.mem_neighborFinset h hminus).mpr hadj) hminusH
    have hplusNotAdj : ¬ G.Adj h hplus := by
      intro hadj
      exact Finset.disjoint_left.mp (hhighIndependent h hhH)
        ((G.mem_neighborFinset h hplus).mpr hadj) hplusH
    simp [hhH, hhS, hminusNotAdj, hplusNotAdj] at heq
    have hZcard : (G.neighborFinset h ∩ Z).card = 10 := by omega
    have hcard : (G.neighborFinset h ∩ Z).card =
        (G.neighborFinset h).card := by
      rw [hZcard, G.card_neighborFinset_eq_degree, hdegHigh h hhH]
    exact Finset.inter_eq_left.mp (Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega :
        (G.neighborFinset h).card ≤ (G.neighborFinset h ∩ Z).card))
  have hownerZdegree : (G.neighborFinset owner ∩ Z).card = 1 := by
    have heq := heq17 owner
    rw [hownerDefect] at heq
    simp [hownerS, hownerH, hownerMinus, hownerPlus] at heq
    omega
  have hpartnersZ : partners ⊆ G.neighborFinset owner ∩ Z := by
    intro p hp
    obtain ⟨h, hhH, hhp⟩ := hpartnersRoot p hp
    exact Finset.mem_inter.mpr ⟨hpartnersOwner hp,
      hrootSaturation h hhH ((G.mem_neighborFinset h p).mpr hhp)⟩
  have hle := Finset.card_le_card hpartnersZ
  rw [hpartnerCard, hownerZdegree] at hle
  omega

#print axioms Erdos85.orderNine_order18_nonsymmetric_defect_equation_of_global_shore_equation
#print axioms Erdos85.false_of_orderNine_order18_nonsymmetric_defect_equation

end Erdos85
