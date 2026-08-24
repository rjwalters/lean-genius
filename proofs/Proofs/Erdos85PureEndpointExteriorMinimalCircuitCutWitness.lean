import Proofs.Erdos85PureEndpointExteriorMinimalEvenConfiguration

/-! # Every split of a minimal binary circuit is crossed oddly -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- A proper nonempty subset of a minimal pointwise-even configuration has a
point of odd incidence, and the complementary subset has odd incidence at
the same point. -/
theorem minimal_even_configuration_exists_odd_cut_point
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc] (T : Finset α)
    (heven : ∀ y : β, Even ((T.filter fun a => Inc a y).card))
    (hminimal : ∀ U : Finset α, U ⊂ T → U.Nonempty →
      ¬ ∀ y : β, Even ((U.filter fun a => Inc a y).card))
    (U : Finset α) (hUT : U ⊂ T) (hU : U.Nonempty) :
    ∃ y : β,
      Odd ((U.filter fun a => Inc a y).card) ∧
      Odd (((T \ U).filter fun a => Inc a y).card) := by
  classical
  have hnot := hminimal U hUT hU
  push_neg at hnot
  obtain ⟨y, hyNot⟩ := hnot
  have hyOdd : Odd ((U.filter fun a => Inc a y).card) :=
    Nat.not_even_iff_odd.mp hyNot
  let A := T.filter fun a => Inc a y
  let B := U.filter fun a => Inc a y
  let C := (T \ U).filter fun a => Inc a y
  have hpart : A = B ∪ C := by
    ext a
    simp only [A, B, C, mem_filter, mem_union, mem_sdiff]
    constructor
    · intro ha
      by_cases haU : a ∈ U
      · exact Or.inl ⟨haU, ha.2⟩
      · exact Or.inr ⟨⟨ha.1, haU⟩, ha.2⟩
    · rintro (⟨haU, haInc⟩ | ⟨⟨haT, _haU⟩, haInc⟩)
      · exact ⟨hUT.1 haU, haInc⟩
      · exact ⟨haT, haInc⟩
  have hdis : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro a haB haC
    exact (mem_sdiff.mp (mem_filter.mp haC).1).2
      (mem_filter.mp haB).1
  have hcard : A.card = B.card + C.card := by
    rw [hpart, card_union_of_disjoint hdis]
  have hAeven : Even A.card := by simpa [A] using heven y
  have hBodd : Odd B.card := by simpa [B] using hyOdd
  rcases hAeven with ⟨r, hr⟩
  rcases hBodd with ⟨s, hs⟩
  have hCodd : Odd C.card := by
    refine ⟨r - s - 1, ?_⟩
    omega
  exact ⟨y, hyOdd, by simpa [C] using hCodd⟩

/-- The extracted minimal endpoint circuit has an odd incidence witness on
both shores of every proper nonempty split. -/
theorem c4Free_binarySquare_pureEndpoint_exists_minimal_even_configuration_cutWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
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
    ∃ T : Finset W, T.Nonempty ∧ m + 1 ≤ T.card ∧
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) ∧
      (∀ U : Finset W, U ⊂ T → U.Nonempty →
        ¬ ∀ y : P, Even ((U.filter fun w => G.Adj w.1 y.1).card)) ∧
      ∀ U : Finset W, U ⊂ T → U.Nonempty →
        ∃ y : P,
          Odd ((U.filter fun w => G.Adj w.1 y.1).card) ∧
          Odd (((T \ U).filter fun w => G.Adj w.1 y.1).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  obtain ⟨T, hT, hlarge, heven, hminimal⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_minimal_even_exteriorRowConfiguration
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  refine ⟨T, hT, hlarge, heven, hminimal, ?_⟩
  intro U hUT hU
  exact minimal_even_configuration_exists_odd_cut_point
    Inc T heven hminimal U hUT hU

end

end Erdos85

#print axioms Erdos85.minimal_even_configuration_exists_odd_cut_point
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_minimal_even_configuration_cutWitness
