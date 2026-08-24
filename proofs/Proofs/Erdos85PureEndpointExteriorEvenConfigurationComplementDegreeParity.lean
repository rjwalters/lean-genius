import Proofs.Erdos85PureEndpointExteriorMinimalCircuitEulerian

/-! # Complement-degree parity of an exterior even configuration -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Partitioning the other selected rows into meeting and nonmeeting rows
transfers even internal degree into the opposite parity for the complement
degree. -/
theorem even_internal_degree_complement_parity
    {α : Type*} [DecidableEq α]
    (T : Finset α) (p : α) (R : α → α → Prop) [DecidableRel R]
    (hp : p ∈ T)
    (hdegree : Even (((T.erase p).filter fun q => R p q).card)) :
    (Odd T.card →
      Even (((T.erase p).filter fun q => ¬ R p q).card)) ∧
    (Even T.card →
      Odd (((T.erase p).filter fun q => ¬ R p q).card)) := by
  classical
  let I := (T.erase p).filter fun q => R p q
  let N := (T.erase p).filter fun q => ¬ R p q
  have hpart : T.erase p = I ∪ N := by
    ext q
    simp only [I, N, mem_erase, mem_union, mem_filter]
    constructor
    · intro hq
      by_cases hR : R p q
      · exact Or.inl ⟨hq, hR⟩
      · exact Or.inr ⟨hq, hR⟩
    · rintro (⟨hq, _hR⟩ | ⟨hq, _hR⟩) <;> exact hq
  have hdis : Disjoint I N := by
    rw [Finset.disjoint_left]
    intro q hqI hqN
    exact (mem_filter.mp hqN).2 (mem_filter.mp hqI).2
  have hcardPart : (T.erase p).card = I.card + N.card := by
    rw [hpart, card_union_of_disjoint hdis]
  have hIle : I.card ≤ (T.erase p).card :=
    card_le_card (filter_subset _ _)
  have hIeven : Even I.card := by simpa [I] using hdegree
  have herase : (T.erase p).card = T.card - 1 := card_erase_of_mem hp
  constructor
  · intro hTcard
    change Even N.card
    rcases hTcard with ⟨a, ha⟩
    have hEraseEven : Even (T.erase p).card := by
      refine ⟨a, ?_⟩
      omega
    rw [hcardPart] at hEraseEven
    exact (Nat.even_add.mp hEraseEven).mp hIeven
  · intro hTcard
    change Odd N.card
    rcases hTcard with ⟨a, ha⟩
    have hpos : 0 < T.card := card_pos.mpr ⟨p, hp⟩
    have haPos : 0 < a := by omega
    have hEraseOdd : Odd (T.erase p).card := by
      refine ⟨a - 1, ?_⟩
      omega
    rw [hcardPart] at hEraseOdd
    have hswap : Odd (N.card + I.card) := by
      simpa [add_comm] using hEraseOdd
    exact (Nat.odd_add.mp hswap).mpr hIeven

/-- For any dyadic endpoint even configuration, an odd circuit has even
row-nondegrees and an even circuit has positive odd row-nondegrees. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_complementDegreeParity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
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
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      ∀ w ∈ T,
        (Odd T.card → Even (((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card)) ∧
        (Even T.card → Odd (((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card)) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven w hw
  have hdegree :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_internalDegreeEven
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven w hw
  exact even_internal_degree_complement_parity T w
    (fun a b => (row a ∩ row b).Nonempty) hw hdegree

end

end Erdos85

#print axioms Erdos85.even_internal_degree_complement_parity
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_complementDegreeParity
