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

/-- A nonsymmetric order-eighteen FullType shore has the sharp explicit
`(6,7)` partition on its 60-point ordinary complement. -/
theorem orderNine_order18_nonsymmetric_explicit_complement_of_fullType
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (E S : Finset V)
    (hfull : orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ S)
    (hSsub : S ⊆ (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hboundary : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = (E ∩ S).card)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅)
    (hS18 : S.card = 18)
    (hnonsym : ¬ ((G.neighborFinset h₁ ∩ S).card = 2 ∧
      (G.neighborFinset h₂ ∩ S).card = 2 ∧
      (G.neighborFinset h₃ ∩ S).card = 2)) :
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃
      (((Finset.univ : Finset V) \ {h₁, h₂, h₃}) \ S) 6 48 := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let R := O \ S
  have hHcard : H.card = 3 := by simp [H, h₁₂, h₁₃, h₂₃]
  have hOcard : O.card = 78 := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ H),
      Finset.card_univ, hcard, hHcard]
  have hRcard : R.card = 60 := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset (by simpa [O, H] using hSsub),
      hOcard, hS18]
  have hRH : Disjoint R H := by
    rw [Finset.disjoint_left]
    intro x hxR hxH
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxR).1).2 hxH
  have hcompBoundary := ordinary_complement_boundary_sum_eq
    (secondOrderDefectGraph G) H S (by simpa [H] using hSsub)
      (by simpa [H] using hdefectHighIsolated)
  have hb₁ := orderNine_high_neighbor_ordinary_compl_card G H S h₁
    (hdegHigh h₁ (by simp [H])) (hhighIndependent h₁ (by simp [H]))
  have hb₂ := orderNine_high_neighbor_ordinary_compl_card G H S h₂
    (hdegHigh h₂ (by simp [H])) (hhighIndependent h₂ (by simp [H]))
  have hb₃ := orderNine_high_neighbor_ordinary_compl_card G H S h₃
    (hdegHigh h₃ (by simp [H])) (hhighIndependent h₃ (by simp [H]))
  have hb₁R : (G.neighborFinset h₁ ∩ R).card =
      10 - (G.neighborFinset h₁ ∩ S).card := by simpa [R, O] using hb₁
  have hb₂R : (G.neighborFinset h₂ ∩ R).card =
      10 - (G.neighborFinset h₂ ∩ S).card := by simpa [R, O] using hb₂
  have hb₃R : (G.neighborFinset h₃ ∩ R).card =
      10 - (G.neighborFinset h₃ ∩ S).card := by simpa [R, O] using hb₃
  have hcomp18 : orderNineNearRegularCutLower (78 - S.card)
      (10 - (G.neighborFinset h₁ ∩ S).card)
      (10 - (G.neighborFinset h₂ ∩ S).card)
      (10 - (G.neighborFinset h₃ ∩ S).card) = 2 := by
    rcases orderNineArticulationSmallShoreBetaType_sharp_dichotomy
      G h₁ h₂ h₃ S hfull.1 with hsym | h18 | h27 | h34
    · exact (hnonsym hsym.2).elim
    · exact h18.2
    · omega
    · omega
  have he : (E ∩ S).card = 2 := hfull.2.1 hS18
  have hsharp := orderNineOrdinarySharpPartition_of_boundary
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R hRH
      (by simpa [H] using hdegOrd) (by simpa [H] using hdegHigh) 2
      (hcompBoundary.trans (hboundary.trans he)) (by
        simpa [R, O, H, hRcard, hS18, hb₁, hb₂, hb₃] using hcomp18)
  apply orderNineOrdinaryExplicitPartition_of_sharp
    G h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ R 6 48 hRH
      (by simpa [H] using hdegOrd) hsharp
  · rw [hRcard, hb₁R, hb₂R, hb₃R]
    have hbeta := hfull.1
    unfold orderNineArticulationSmallShoreBetaType at hbeta
    rcases hbeta with ⟨hs, hb⟩ | ⟨hs, hb₁', hb₂', hb₃'⟩ |
        ⟨hs, hb₁', hb₂', hb₃'⟩
    · rcases hb with hb | hb | hb | hb | hb | hb | hb <;>
        rcases hb with ⟨hb₁', hb₂', hb₃'⟩ <;> omega
    all_goals omega
  · norm_num

/-- Root-order-invariant version of equation (16).  The explicit partition
uses a fixed enumeration of `H`; the signed correction vertices may be any
two roots, with their high-root values supplied pointwise. -/
theorem orderNine_order18_nonsymmetric_global_shore_equation_general
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ hminus hplus : V) (S R : Finset V)
    (hunion : S ∪ R = (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hdisj : Disjoint S R)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) {h₁, h₂, h₃})
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 6 48)
    (hminusH : hminus ∈ ({h₁, h₂, h₃} : Finset V))
    (hplusH : hplus ∈ ({h₁, h₂, h₃} : Finset V))
    (hbeta : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      ((G.neighborFinset h ∩ S).card : ℤ) =
        2 - (if h = hminus then 1 else 0) +
          (if h = hplus then 1 else 0)) :
    let H : Finset V := {h₁, h₂, h₃}
    let Z := orderNineOrdinaryLowSet G h₁ h₂ h₃ R 6
    ∀ x : V,
      ((G.neighborFinset x ∩ S).card : ℤ) =
        2 + (if x ∈ Z then 1 else 0) -
          ((G.neighborFinset x ∩ H).card : ℤ) -
          (if x = hminus then 1 else 0) +
          (if x = hplus then 1 else 0) := by
  classical
  dsimp only
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let Z := orderNineOrdinaryLowSet G h₁ h₂ h₃ R 6
  have hZsub : Z ⊆ O := orderNineOrdinaryLowSet_subset G h₁ h₂ h₃ R 6
  have hSRwhole : S ∪ R = O := by simpa [O, H] using hunion
  intro x
  change ((G.neighborFinset x ∩ S).card : ℤ) =
    2 + (if x ∈ Z then 1 else 0) -
      ((G.neighborFinset x ∩ H).card : ℤ) -
      (if x = hminus then 1 else 0) +
      (if x = hplus then 1 else 0)
  by_cases hxH : x ∈ H
  · have hxZ : x ∉ Z := fun hxZ ↦
      (Finset.mem_sdiff.mp (hZsub hxZ)).2 hxH
    have hNH : (G.neighborFinset x ∩ H).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.eq_empty_iff_forall_notMem.mpr fun y hy ↦
        Finset.disjoint_left.mp (hhighIndependent x (by simpa [H] using hxH))
          (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
    rw [if_neg hxZ, hNH]
    simpa [H] using hbeta x (by simpa [H] using hxH)
  · have hxO : x ∈ O := by simp [O, hxH]
    have hlevels := hpart.1 ⟨x, hxO⟩
    change (G.neighborFinset x ∩ R).card = 6 ∨
      (G.neighborFinset x ∩ R).card = 7 at hlevels
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
    have hxDegree : G.degree x = 9 := hdegOrd x (by simpa [H] using hxH)
    have hxMinus : x ≠ hminus := fun hxm ↦ hxH (by simpa [H, hxm] using hminusH)
    have hxPlus : x ≠ hplus := fun hxp ↦ hxH (by simpa [H, hxp] using hplusH)
    rcases hlevels with hlow | hupp
    · have hxZ : x ∈ Z := by
        simp [Z, orderNineOrdinaryLowSet, O, H, hxO, hlow]
      rw [hlow] at hcardSR
      rw [hxDegree] at hcardOH
      rw [if_pos hxZ, if_neg hxMinus, if_neg hxPlus]
      omega
    · have hxZ : x ∉ Z := by
        simp [Z, orderNineOrdinaryLowSet, O, H, hxO, hupp]
      rw [hupp] at hcardSR
      rw [hxDegree] at hcardOH
      rw [if_neg hxZ, if_neg hxMinus, if_neg hxPlus]
      omega

/-- Fixed-root nonsymmetric capstone, avoiding any transport of subtype
partitions across permutations of the named high roots. -/
theorem false_of_orderNine_order18_nonsymmetric_fixedRoots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (h₁ h₂ h₃ hminus hplus : V) (S R : Finset V)
    (hunion : S ∪ R = (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hdisj : Disjoint S R) (hScard : S.card = 18)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) {h₁, h₂, h₃})
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 6 48)
    (hHcard : ({h₁, h₂, h₃} : Finset V).card = 3)
    (hminusH : hminus ∈ ({h₁, h₂, h₃} : Finset V))
    (hplusH : hplus ∈ ({h₁, h₂, h₃} : Finset V))
    (hbeta : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      ((G.neighborFinset h ∩ S).card : ℤ) =
        2 - (if h = hminus then 1 else 0) +
          (if h = hplus then 1 else 0))
    (owner : V) (hownerS : owner ∉ S)
    (hownerH : owner ∉ ({h₁, h₂, h₃} : Finset V))
    (hownerMinus : G.Adj owner hminus) (hownerPlus : G.Adj owner hplus)
    (hownerDefect :
      ((secondOrderDefectGraph G).neighborFinset owner ∩ S).card = 2)
    (partners : Finset V) (hpartnerCard : partners.card = 3)
    (hpartnersOwner : partners ⊆ G.neighborFinset owner)
    (hpartnersRoot : ∀ p ∈ partners,
      ∃ h ∈ ({h₁, h₂, h₃} : Finset V), G.Adj h p) : False := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let Z := orderNineOrdinaryLowSet G h₁ h₂ h₃ R 6
  have hSsub : S ⊆ (Finset.univ : Finset V) \ H := by
    intro x hxS
    have hx := Finset.mem_union_left R hxS
    rw [hunion] at hx
    simpa [H] using hx
  have hSH : Disjoint S H := by
    rw [Finset.disjoint_left]
    exact fun x hxS hxH ↦ (Finset.mem_sdiff.mp (hSsub hxS)).2 hxH
  have hglobal := orderNine_order18_nonsymmetric_global_shore_equation_general
    G h₁ h₂ h₃ hminus hplus S R hunion hdisj hdegOrd
      hhighIndependent hpart hminusH hplusH hbeta
  have heq17 :=
    orderNine_order18_nonsymmetric_defect_equation_of_global_shore_equation
      G hfree H S Z hminus hplus (by simpa [H] using hHcard) hScard hSH
        (by simpa [H] using hdegOrd) (by simpa [H] using hdegHigh)
        (by simpa [H] using hdefectHighIsolated) (by simpa [H, Z] using hglobal)
  exact false_of_orderNine_order18_nonsymmetric_defect_equation
    G (secondOrderDefectGraph G) H S Z partners owner hminus hplus hSH
      hownerS (by simpa [H] using hownerH) (by simpa [H] using hminusH)
      (by simpa [H] using hplusH) (by simpa [H] using hhighIndependent)
      (by simpa [H] using hdegHigh) (by simpa [H] using hdefectHighIsolated)
      hownerMinus hownerPlus hownerDefect heq17 hpartnerCard hpartnersOwner
      (by simpa [H] using hpartnersRoot)

/- Disabled first dispatcher draft; retained temporarily while the invariant
fixed-root formulation below replaces root-order rewriting. -/
/-
/-- Full permutation dispatcher: under the owner/partner data of the second
profile, an order-eighteen FullType shore must have symmetric beta `(2,2,2)`.
All six permutations of `(1,2,3)` feed the preceding nonsymmetric capstone. -/
theorem orderNine_order18_fullType_beta_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (E S : Finset V)
    (hfull : orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ S)
    (hSsub : S ⊆ (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hboundary : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = (E ∩ S).card)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅)
    (owner : V) (hownerS : owner ∉ S)
    (hownerH : owner ∉ ({h₁, h₂, h₃} : Finset V))
    (hownerAdj : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.Adj owner h)
    (hownerDefect :
      ((secondOrderDefectGraph G).neighborFinset owner ∩ S).card = 2)
    (partners : Finset V) (hpartnerCard : partners.card = 3)
    (hpartnersOwner : partners ⊆ G.neighborFinset owner)
    (hpartnersRoot : ∀ p ∈ partners,
      ∃ h ∈ ({h₁, h₂, h₃} : Finset V), G.Adj h p) :
    S.card = 18 ∧
      (G.neighborFinset h₁ ∩ S).card = 2 ∧
      (G.neighborFinset h₂ ∩ S).card = 2 ∧
      (G.neighborFinset h₃ ∩ S).card = 2 := by
  classical
  have hbeta := hfull.1
  unfold orderNineArticulationSmallShoreBetaType at hbeta
  rcases hbeta with ⟨hS18, hcases⟩ | h27 | h34
  · rcases hcases with hsym | h123 | h132 | h213 | h231 | h312 | h321
    · exact ⟨hS18, hsym⟩
    all_goals
      have hnonsym : ¬ ((G.neighborFinset h₁ ∩ S).card = 2 ∧
          (G.neighborFinset h₂ ∩ S).card = 2 ∧
          (G.neighborFinset h₃ ∩ S).card = 2) := by omega
      have hpart := orderNine_order18_nonsymmetric_explicit_complement_of_fullType
        G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ E S hfull hSsub
          hboundary hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
          hS18 hnonsym
      let H : Finset V := {h₁, h₂, h₃}
      let O := (Finset.univ : Finset V) \ H
      let R := O \ S
      have hSsubO : S ⊆ O := by simpa [O, H] using hSsub
      have hunionR : S ∪ R = O := by
        dsimp [R]
        exact Finset.union_sdiff_of_subset hSsubO
    · exact (false_of_orderNine_order18_nonsymmetric_explicit_complement
        G hfree h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ S R
          (by simpa [O, H] using hunionR) (by
            dsimp [R]; exact Finset.disjoint_sdiff_right) hS18 hdegOrd
          hdegHigh hhighIndependent hdefectHighIsolated
          h123.1 h123.2.1 h123.2.2 (by simpa [R, O, H] using hpart)
          owner hownerS hownerH (hownerAdj h₁ (by simp))
          (hownerAdj h₃ (by simp)) hownerDefect partners hpartnerCard
          hpartnersOwner hpartnersRoot).elim
    · exact (false_of_orderNine_order18_nonsymmetric_explicit_complement
        G hfree h₁ h₃ h₂ h₁₃ h₁₂ (Ne.symm h₂₃) S R
          (by simpa [O, H, Finset.pair_comm] using hunionR) (by
            dsimp [R]; exact Finset.disjoint_sdiff_right) hS18
          (by simpa [Finset.pair_comm] using hdegOrd)
          (by simpa [Finset.pair_comm] using hdegHigh)
          (by simpa [Finset.pair_comm] using hhighIndependent)
          (by simpa [Finset.pair_comm] using hdefectHighIsolated)
          h132.1 h132.2.2 h132.2.1
          (by simpa [R, O, H, orderNineOrdinaryExplicitPartition,
            Finset.pair_comm] using hpart)
          owner hownerS (by simpa [Finset.pair_comm] using hownerH)
          (hownerAdj h₁ (by simp)) (hownerAdj h₂ (by simp)) hownerDefect
          partners hpartnerCard hpartnersOwner
          (by simpa [Finset.pair_comm] using hpartnersRoot)).elim
    · exact (false_of_orderNine_order18_nonsymmetric_explicit_complement
        G hfree h₂ h₁ h₃ (Ne.symm h₁₂) h₂₃ h₁₃ S R
          (by simpa [O, H, Finset.pair_comm] using hunionR) (by
            dsimp [R]; exact Finset.disjoint_sdiff_right) hS18
          (by simpa [Finset.pair_comm] using hdegOrd)
          (by simpa [Finset.pair_comm] using hdegHigh)
          (by simpa [Finset.pair_comm] using hhighIndependent)
          (by simpa [Finset.pair_comm] using hdefectHighIsolated)
          h213.2.1 h213.1 h213.2.2
          (by simpa [R, O, H, orderNineOrdinaryExplicitPartition,
            Finset.pair_comm] using hpart)
          owner hownerS (by simpa [Finset.pair_comm] using hownerH)
          (hownerAdj h₂ (by simp)) (hownerAdj h₃ (by simp)) hownerDefect
          partners hpartnerCard hpartnersOwner
          (by simpa [Finset.pair_comm] using hpartnersRoot)).elim
    · exact (false_of_orderNine_order18_nonsymmetric_explicit_complement
        G hfree h₃ h₁ h₂ (Ne.symm h₁₃) (Ne.symm h₂₃) h₁₂ S R
          (by simpa [O, H, Finset.pair_comm] using hunionR) (by
            dsimp [R]; exact Finset.disjoint_sdiff_right) hS18
          (by simpa [Finset.pair_comm] using hdegOrd)
          (by simpa [Finset.pair_comm] using hdegHigh)
          (by simpa [Finset.pair_comm] using hhighIndependent)
          (by simpa [Finset.pair_comm] using hdefectHighIsolated)
          h231.2.2 h231.1 h231.2.1
          (by simpa [R, O, H, orderNineOrdinaryExplicitPartition,
            Finset.pair_comm] using hpart)
          owner hownerS (by simpa [Finset.pair_comm] using hownerH)
          (hownerAdj h₃ (by simp)) (hownerAdj h₂ (by simp)) hownerDefect
          partners hpartnerCard hpartnersOwner
          (by simpa [Finset.pair_comm] using hpartnersRoot)).elim
    · exact (false_of_orderNine_order18_nonsymmetric_explicit_complement
        G hfree h₂ h₃ h₁ h₂₃ (Ne.symm h₁₂) (Ne.symm h₁₃) S R
          (by simpa [O, H, Finset.pair_comm] using hunionR) (by
            dsimp [R]; exact Finset.disjoint_sdiff_right) hS18
          (by simpa [Finset.pair_comm] using hdegOrd)
          (by simpa [Finset.pair_comm] using hdegHigh)
          (by simpa [Finset.pair_comm] using hhighIndependent)
          (by simpa [Finset.pair_comm] using hdefectHighIsolated)
          h312.2.1 h312.2.2 h312.1
          (by simpa [R, O, H, orderNineOrdinaryExplicitPartition,
            Finset.pair_comm] using hpart)
          owner hownerS (by simpa [Finset.pair_comm] using hownerH)
          (hownerAdj h₂ (by simp)) (hownerAdj h₁ (by simp)) hownerDefect
          partners hpartnerCard hpartnersOwner
          (by simpa [Finset.pair_comm] using hpartnersRoot)).elim
    · exact (false_of_orderNine_order18_nonsymmetric_explicit_complement
        G hfree h₃ h₂ h₁ (Ne.symm h₂₃) (Ne.symm h₁₃)
          (Ne.symm h₁₂) S R
          (by simpa [O, H, Finset.pair_comm] using hunionR) (by
            dsimp [R]; exact Finset.disjoint_sdiff_right) hS18
          (by simpa [Finset.pair_comm] using hdegOrd)
          (by simpa [Finset.pair_comm] using hdegHigh)
          (by simpa [Finset.pair_comm] using hhighIndependent)
          (by simpa [Finset.pair_comm] using hdefectHighIsolated)
          h321.2.2 h321.2.1 h321.1
          (by simpa [R, O, H, orderNineOrdinaryExplicitPartition,
            Finset.pair_comm] using hpart)
          owner hownerS (by simpa [Finset.pair_comm] using hownerH)
          (hownerAdj h₃ (by simp)) (hownerAdj h₁ (by simp)) hownerDefect
          partners hpartnerCard hpartnersOwner
          (by simpa [Finset.pair_comm] using hpartnersRoot)).elim
  · omega
  · omega

-/

#print axioms Erdos85.orderNine_order18_nonsymmetric_global_shore_equation
#print axioms Erdos85.orderNine_order18_nonsymmetric_defect_equation_of_global_shore_equation
#print axioms Erdos85.false_of_orderNine_order18_nonsymmetric_defect_equation
#print axioms Erdos85.false_of_orderNine_order18_nonsymmetric_explicit_complement
#print axioms Erdos85.orderNine_order18_nonsymmetric_explicit_complement_of_fullType
#print axioms Erdos85.orderNine_order18_nonsymmetric_global_shore_equation_general
#print axioms Erdos85.false_of_orderNine_order18_nonsymmetric_fixedRoots

end Erdos85
