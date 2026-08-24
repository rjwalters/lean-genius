import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddThreeQuarticIncidence

/-! # Odd degree-two complement sector at the `m+3` stratum -/

open Finset BigOperators

namespace Erdos85

noncomputable section

set_option maxHeartbeats 1600000

/-- In a disjoint partition of an odd finite set, an even left shore forces
an odd right shore. -/
theorem odd_card_right_of_disjoint_union
    {α : Type*} [DecidableEq α] (T R₀ R₂ : Finset α)
    (hpart : T = R₀ ∪ R₂) (hdis : Disjoint R₀ R₂)
    (hTodd : Odd T.card) (hR₀even : Even R₀.card) : Odd R₂.card := by
  have hcard : T.card = R₀.card + R₂.card := by
    rw [hpart, card_union_of_disjoint hdis]
  rcases hTodd with ⟨a, ha⟩
  rcases hR₀even with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  omega

/-- In an endpoint exterior even configuration with `|T|=m+3`, an odd
number of rows have exactly two nonmeeting partners. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_degreeTwoSectorOdd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcardV : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 3 →
      Odd ((T.filter fun w =>
        ((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card = 2).card) := by
  classical
  dsimp only
  intro T heven hTcard
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let R₀ := T.filter fun w =>
    ((T.erase w).filter fun u => ¬ (row w ∩ row u).Nonempty).card = 0
  let R₂ := T.filter fun w =>
    ((T.erase w).filter fun u => ¬ (row w ∩ row u).Nonempty).card = 2
  let Q := (T.biUnion row).filter fun y =>
    (T.filter fun w => y ∈ row w).card = 4
  have hbalance : R₀.card = 4 * Q.card := by
    have hb :=
      c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_quarticBalance
        G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
        T heven hTcard
    change R₀.card = 4 * Q.card at hb
    exact hb
  have hmissing :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_complementDegree
      G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
      T heven hTcard
  have hmissingRow : ∀ w ∈ T,
      ((T.erase w).filter fun u => ¬ (row w ∩ row u).Nonempty).card = 0 ∨
      ((T.erase w).filter fun u => ¬ (row w ∩ row u).Nonempty).card = 2 := by
    intro w hw
    have hm := hmissing w hw
    change ((T.erase w).filter fun u =>
      ¬ ((G.neighborFinset w.1 ∩ S) ∩
        (G.neighborFinset u.1 ∩ S)).Nonempty).card = 0 ∨
      ((T.erase w).filter fun u =>
      ¬ ((G.neighborFinset w.1 ∩ S) ∩
        (G.neighborFinset u.1 ∩ S)).Nonempty).card = 2
    simpa only [inter_assoc] using hm
  have hpart : T = R₀ ∪ R₂ := by
    ext w
    simp only [R₀, R₂, mem_union, mem_filter]
    constructor
    · intro hw
      rcases hmissingRow w hw with hzero | htwo
      · exact Or.inl ⟨hw, hzero⟩
      · exact Or.inr ⟨hw, htwo⟩
    · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
  have hdis : Disjoint R₀ R₂ := by
    rw [disjoint_left]
    intro w hw₀ hw₂
    have hzero := (mem_filter.mp hw₀).2
    have htwo := (mem_filter.mp hw₂).2
    omega
  have hTodd : Odd T.card := by
    rcases hmEven with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    omega
  have hR₀even : Even R₀.card := by
    refine ⟨2 * Q.card, ?_⟩
    omega
  change Odd R₂.card
  exact odd_card_right_of_disjoint_union
    T R₀ R₂ hpart hdis hTodd hR₀even

end

end Erdos85

#print axioms Erdos85.odd_card_right_of_disjoint_union
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_degreeTwoSectorOdd
