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

/-- The equality profile on the 60-point complementary shore gives audit
equation (16) on the order-eighteen shore with boundary triple `(1,2,3)`. -/
theorem orderNine_order18_nonsymmetric_global_shore_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hminus hmiddle hplus : V)
    (hminusMiddle : hminus ≠ hmiddle)
    (hminusPlus : hminus ≠ hplus)
    (hmiddlePlus : hmiddle ≠ hplus)
    (S R : Finset V)
    (hunion : S ∪ R = (Finset.univ : Finset V) \
      {hminus, hmiddle, hplus})
    (hdisj : Disjoint S R)
    (hdegOrd : ∀ x ∉ ({hminus, hmiddle, hplus} : Finset V),
      G.degree x = 9)
    (hhighIndependent : ∀ h ∈ ({hminus, hmiddle, hplus} : Finset V),
      Disjoint (G.neighborFinset h) {hminus, hmiddle, hplus})
    (hbetaMinus : (G.neighborFinset hminus ∩ S).card = 1)
    (hbetaMiddle : (G.neighborFinset hmiddle ∩ S).card = 2)
    (hbetaPlus : (G.neighborFinset hplus ∩ S).card = 3)
    (hpart : orderNineOrdinaryExplicitPartition G hminus hmiddle hplus R 6 48) :
    let H : Finset V := {hminus, hmiddle, hplus}
    let Z := orderNineOrdinaryLowSet G hminus hmiddle hplus R 6
    ∀ x : V,
      ((G.neighborFinset x ∩ S).card : ℤ) =
        2 + (if x ∈ Z then 1 else 0) -
          ((G.neighborFinset x ∩ H).card : ℤ) -
          (if x = hminus then 1 else 0) +
          (if x = hplus then 1 else 0) := by
  classical
  dsimp only
  let H : Finset V := {hminus, hmiddle, hplus}
  let O := (Finset.univ : Finset V) \ H
  let Z := orderNineOrdinaryLowSet G hminus hmiddle hplus R 6
  have hZsub : Z ⊆ O := by
    exact orderNineOrdinaryLowSet_subset G hminus hmiddle hplus R 6
  intro x
  change ((G.neighborFinset x ∩ S).card : ℤ) =
    2 + (if x ∈ Z then 1 else 0) -
      ((G.neighborFinset x ∩ H).card : ℤ) -
      (if x = hminus then 1 else 0) +
      (if x = hplus then 1 else 0)
  by_cases hxMinus : x = hminus
  · subst x
    have hxH : hminus ∈ H := by simp [H]
    have hxZ : hminus ∉ Z := fun hxZ ↦ (Finset.mem_sdiff.mp (hZsub hxZ)).2 hxH
    have hNH : (G.neighborFinset hminus ∩ H).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.eq_empty_iff_forall_notMem.mpr fun y hy ↦
        Finset.disjoint_left.mp (hhighIndependent hminus (by simp [H]))
          (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
    have hxZ' : hminus ∉
        orderNineOrdinaryLowSet G hminus hmiddle hplus R 6 := by exact hxZ
    have hNH' : (G.neighborFinset hminus ∩
        ({hminus, hmiddle, hplus} : Finset V)).card = 0 := by
      simpa [H] using hNH
    rw [hbetaMinus, hNH']
    rw [if_neg hxZ]
    simp [hminusPlus]
  by_cases hxMiddle : x = hmiddle
  · subst x
    have hxH : hmiddle ∈ H := by simp [H]
    have hxZ : hmiddle ∉ Z := fun hxZ ↦ (Finset.mem_sdiff.mp (hZsub hxZ)).2 hxH
    have hNH : (G.neighborFinset hmiddle ∩ H).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.eq_empty_iff_forall_notMem.mpr fun y hy ↦
        Finset.disjoint_left.mp (hhighIndependent hmiddle (by simp [H]))
          (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
    have hxZ' : hmiddle ∉
        orderNineOrdinaryLowSet G hminus hmiddle hplus R 6 := by exact hxZ
    have hNH' : (G.neighborFinset hmiddle ∩
        ({hminus, hmiddle, hplus} : Finset V)).card = 0 := by
      simpa [H] using hNH
    rw [hbetaMiddle, hNH']
    rw [if_neg hxZ]
    simp [hxMinus, hmiddlePlus]
  by_cases hxPlus : x = hplus
  · subst x
    have hxH : hplus ∈ H := by simp [H]
    have hxZ : hplus ∉ Z := fun hxZ ↦ (Finset.mem_sdiff.mp (hZsub hxZ)).2 hxH
    have hNH : (G.neighborFinset hplus ∩ H).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.eq_empty_iff_forall_notMem.mpr fun y hy ↦
        Finset.disjoint_left.mp (hhighIndependent hplus (by simp [H]))
          (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
    have hxZ' : hplus ∉
        orderNineOrdinaryLowSet G hminus hmiddle hplus R 6 := by exact hxZ
    have hNH' : (G.neighborFinset hplus ∩
        ({hminus, hmiddle, hplus} : Finset V)).card = 0 := by
      simpa [H] using hNH
    rw [hbetaPlus, hNH']
    rw [if_neg hxZ]
    simp [hxMinus]
  have hxNotH : x ∉ H := by simp [H, hxMinus, hxMiddle, hxPlus]
  have hxO : x ∈ O := by simp [O, hxNotH]
  have hSRwhole : S ∪ R = O := by simpa [O, H] using hunion
  have hlevels := hpart.1 ⟨x, hxO⟩
  change (G.neighborFinset x ∩ R).card = 6 ∨
    (G.neighborFinset x ∩ R).card = 7 at hlevels
  have hSR : (G.neighborFinset x ∩ S).card +
      (G.neighborFinset x ∩ R).card +
      (G.neighborFinset x ∩ H).card = G.degree x := by
    have hSRunion : (G.neighborFinset x ∩ S) ∪
        (G.neighborFinset x ∩ R) = G.neighborFinset x ∩ O := by
      rw [← Finset.inter_union_distrib_left, hSRwhole]
    have hSRdisj : Disjoint (G.neighborFinset x ∩ S)
        (G.neighborFinset x ∩ R) :=
      hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have hOHunion : (G.neighborFinset x ∩ O) ∪
        (G.neighborFinset x ∩ H) = G.neighborFinset x := by
      ext y
      by_cases hyH : y ∈ H <;> simp [O, hyH]
    have hOHdisj : Disjoint (G.neighborFinset x ∩ O)
        (G.neighborFinset x ∩ H) := by
      rw [Finset.disjoint_left]
      intro y hyO hyH
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hyO).2).2
        (Finset.mem_inter.mp hyH).2
    have hcardSR := Finset.card_union_of_disjoint hSRdisj
    rw [hSRunion] at hcardSR
    have hcardOH := Finset.card_union_of_disjoint hOHdisj
    rw [hOHunion, G.card_neighborFinset_eq_degree] at hcardOH
    omega
  have hxDegree : G.degree x = 9 := hdegOrd x (by simpa [H] using hxNotH)
  rcases hlevels with hlow | hupp
  · have hxZ : x ∈ Z := by
      simp [Z, orderNineOrdinaryLowSet, O, H, hxO, hlow]
    rw [hxDegree, hlow] at hSR
    rw [if_pos hxZ, if_neg hxMinus, if_neg hxPlus]
    omega
  · have hxZ : x ∉ Z := by
      simp [Z, orderNineOrdinaryLowSet, O, H, hxO, hupp]
    rw [hxDegree, hupp] at hSR
    rw [if_neg hxZ, if_neg hxMinus, if_neg hxPlus]
    omega

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

/-- Complete nonsymmetric local capstone once the equality complement has
been exposed as the explicit `(6,7)` partition. -/
theorem false_of_orderNine_order18_nonsymmetric_explicit_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hminus hmiddle hplus : V)
    (hminusMiddle : hminus ≠ hmiddle)
    (hminusPlus : hminus ≠ hplus)
    (hmiddlePlus : hmiddle ≠ hplus)
    (S R : Finset V)
    (hunion : S ∪ R = (Finset.univ : Finset V) \
      {hminus, hmiddle, hplus})
    (hdisj : Disjoint S R) (hScard : S.card = 18)
    (hdegOrd : ∀ x ∉ ({hminus, hmiddle, hplus} : Finset V),
      G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({hminus, hmiddle, hplus} : Finset V),
      G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({hminus, hmiddle, hplus} : Finset V),
      Disjoint (G.neighborFinset h) {hminus, hmiddle, hplus})
    (hdefectHighIsolated : ∀ h ∈ ({hminus, hmiddle, hplus} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅)
    (hbetaMinus : (G.neighborFinset hminus ∩ S).card = 1)
    (hbetaMiddle : (G.neighborFinset hmiddle ∩ S).card = 2)
    (hbetaPlus : (G.neighborFinset hplus ∩ S).card = 3)
    (hpart : orderNineOrdinaryExplicitPartition G hminus hmiddle hplus R 6 48)
    (owner : V) (hownerS : owner ∉ S)
    (hownerH : owner ∉ ({hminus, hmiddle, hplus} : Finset V))
    (hownerMinus : G.Adj owner hminus)
    (hownerPlus : G.Adj owner hplus)
    (hownerDefect : ((secondOrderDefectGraph G).neighborFinset owner ∩ S).card = 2)
    (partners : Finset V) (hpartnerCard : partners.card = 3)
    (hpartnersOwner : partners ⊆ G.neighborFinset owner)
    (hpartnersRoot : ∀ p ∈ partners,
      ∃ h ∈ ({hminus, hmiddle, hplus} : Finset V), G.Adj h p) : False := by
  classical
  let H : Finset V := {hminus, hmiddle, hplus}
  let Z := orderNineOrdinaryLowSet G hminus hmiddle hplus R 6
  have hSsub : S ⊆ (Finset.univ : Finset V) \ H := by
    intro x hxS
    have hxUnion : x ∈ S ∪ R := Finset.mem_union_left R hxS
    rw [hunion] at hxUnion
    simpa [H] using hxUnion
  have hSH : Disjoint S H := by
    rw [Finset.disjoint_left]
    intro x hxS hxH
    exact (Finset.mem_sdiff.mp (hSsub hxS)).2 hxH
  have hglobal : ∀ x : V,
      ((G.neighborFinset x ∩ S).card : ℤ) =
        2 + (if x ∈ Z then 1 else 0) -
          ((G.neighborFinset x ∩ H).card : ℤ) -
          (if x = hminus then 1 else 0) +
          (if x = hplus then 1 else 0) := by
    simpa [H, Z] using
      (orderNine_order18_nonsymmetric_global_shore_equation
        G hminus hmiddle hplus hminusMiddle hminusPlus hmiddlePlus
          S R hunion hdisj hdegOrd hhighIndependent hbetaMinus
          hbetaMiddle hbetaPlus hpart)
  have heq17 :=
    orderNine_order18_nonsymmetric_defect_equation_of_global_shore_equation
      G hfree H S Z hminus hplus (by simp [H, hminusMiddle,
        hminusPlus, hmiddlePlus]) hScard hSH
        (by simpa [H] using hdegOrd) (by simpa [H] using hdegHigh)
        (by simpa [H] using hdefectHighIsolated) hglobal
  exact false_of_orderNine_order18_nonsymmetric_defect_equation
    G (secondOrderDefectGraph G) H S Z partners owner hminus hplus hSH
      hownerS (by simpa [H] using hownerH) (by simp [H]) (by simp [H])
      (by simpa [H] using hhighIndependent) (by simpa [H] using hdegHigh)
      (by simpa [H] using hdefectHighIsolated) hownerMinus hownerPlus
      hownerDefect heq17 hpartnerCard hpartnersOwner
      (by simpa [H] using hpartnersRoot)

#print axioms Erdos85.orderNine_order18_nonsymmetric_global_shore_equation
#print axioms Erdos85.orderNine_order18_nonsymmetric_defect_equation_of_global_shore_equation
#print axioms Erdos85.false_of_orderNine_order18_nonsymmetric_defect_equation
#print axioms Erdos85.false_of_orderNine_order18_nonsymmetric_explicit_complement

end Erdos85
