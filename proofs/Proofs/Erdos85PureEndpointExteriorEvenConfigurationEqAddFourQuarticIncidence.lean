import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddFourLocalMultiplicity
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddThreeQuarticIncidence

/-! # Quartic-incidence balance in an `m+4` configuration -/

open Finset BigOperators

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- Under the `m+4` local dichotomy, rows with one nonpartner are counted
four-to-one by multiplicity-four points. -/
theorem localMultiplicityOneThree_quarticIncidence_balance
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α)
    (hloc : ∀ w ∈ T,
      ((((T.erase w).filter fun u =>
          ¬(B w ∩ B u).Nonempty).card = 3 ∧
        ∀ y ∈ B w, (T.filter fun u => y ∈ B u).card = 2) ∨
       (((T.erase w).filter fun u =>
          ¬(B w ∩ B u).Nonempty).card = 1 ∧
        ∃! y, y ∈ B w ∧ (T.filter fun u => y ∈ B u).card = 4 ∧
          ∀ z ∈ B w, z ≠ y →
            (T.filter fun u => z ∈ B u).card = 2))) :
    let R := T.filter fun w =>
      ((T.erase w).filter fun u => ¬(B w ∩ B u).Nonempty).card = 1
    let Q := (T.biUnion B).filter fun y =>
      (T.filter fun w => y ∈ B w).card = 4
    R.card = 4 * Q.card := by
  classical
  dsimp only
  let R := T.filter fun w =>
    ((T.erase w).filter fun u => ¬(B w ∩ B u).Nonempty).card = 1
  let Q := (T.biUnion B).filter fun y =>
    (T.filter fun w => y ∈ B w).card = 4
  have hrow : ∀ w ∈ R, (Q.filter fun y => y ∈ B w).card = 1 := by
    intro w hwR
    have hwData := mem_filter.mp hwR
    rcases hloc w hwData.1 with hthree | hone
    · omega
    · obtain ⟨y, hy, _huniq⟩ := hone.2
      rw [card_eq_one]
      refine ⟨y, ?_⟩
      ext z
      constructor
      · intro hz
        have hzData := mem_filter.mp hz
        have hzEq : z = y := by
          by_contra hzy
          have hzTwo := hy.2.2 z hzData.2 hzy
          have hzFour := (mem_filter.mp hzData.1).2
          omega
        simpa only [mem_singleton] using hzEq
      · intro hz
        have hzEq : z = y := by simpa only [mem_singleton] using hz
        subst z
        exact mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_biUnion.mpr ⟨w, hwData.1, hy.1⟩, hy.2.1⟩, hy.1⟩
  have hcol : ∀ y ∈ Q, (R.filter fun w => y ∈ B w).card = 4 := by
    intro y hyQ
    have hyData := mem_filter.mp hyQ
    have hsub : R.filter (fun w => y ∈ B w) =
        T.filter (fun w => y ∈ B w) := by
      ext w
      simp only [mem_filter, R]
      constructor
      · rintro ⟨⟨hwT, _⟩, hyw⟩
        exact ⟨hwT, hyw⟩
      · rintro ⟨hwT, hyw⟩
        refine ⟨⟨hwT, ?_⟩, hyw⟩
        rcases hloc w hwT with hthree | hone
        · have := hthree.2 y hyw
          omega
        · exact hone.1
    rw [hsub]
    exact hyData.2
  exact card_eq_four_mul_card_of_row_one_col_four
    R Q (fun w y => y ∈ B w) hrow hcol

/-- At the endpoint, the number of `m+4` circuit rows with one nonpartner is
four times the number of used multiplicity-four shore points. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_quarticBalance
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
      T.card = m + 4 →
      let R := T.filter fun w =>
        ((T.erase w).filter fun u => ¬(row w ∩ row u).Nonempty).card = 1
      let Q := (T.biUnion row).filter fun y =>
        (T.filter fun w => y ∈ row w).card = 4
      R.card = 4 * Q.card := by
  classical
  dsimp only
  intro T heven hTcard
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  have hloc :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_localMultiplicity
      G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
      T heven hTcard
  exact localMultiplicityOneThree_quarticIncidence_balance row T hloc

end

end Erdos85

#print axioms Erdos85.localMultiplicityOneThree_quarticIncidence_balance
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_quarticBalance
