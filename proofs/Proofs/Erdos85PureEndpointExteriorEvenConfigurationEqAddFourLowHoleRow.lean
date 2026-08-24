import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddFourPrivateSupport
import Proofs.Erdos85PureEndpointExteriorRowIntersectionDegree

/-! # A low-hole row in an `m+4` circuit -/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- If `m+4` nonnegative weights have total at most `8m`, one is at most
seven. -/
theorem exists_le_seven_of_card_eq_add_four_of_sum_le_eight_mul
    {α : Type*} [DecidableEq α]
    (T : Finset α) (f : α → ℕ) (m : ℕ)
    (hcard : T.card = m + 4)
    (hsum : (∑ x ∈ T, f x) ≤ 8 * m) :
    ∃ x ∈ T, f x ≤ 7 := by
  classical
  by_contra h
  have hall : ∀ x ∈ T, 8 ≤ f x := by
    intro x hx
    have hnle : ¬f x ≤ 7 := by
      intro hle
      exact h ⟨x, hx, hle⟩
    omega
  have hlow : 8 * T.card ≤ ∑ x ∈ T, f x := by
    calc
      8 * T.card = ∑ x ∈ T, 8 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ T, f x := by
        apply sum_le_sum
        intro x hx
        exact hall x hx
  rw [hcard] at hlow
  omega

set_option maxHeartbeats 800000 in
/-- Every endpoint `m+4` even configuration contains a row with at most
seven full-center holes, hence with ambient exterior meeting degree at most
`m(q-3)+7`. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_exists_lowHoleRow
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
    let row := fun w : V => G.neighborFinset w ∩ S
    let K := fun w : V =>
      (secondOrderDefectGraph G).neighborFinset w ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 4 →
      ∃ w ∈ T,
        (K w.1).card ≤ 7 ∧
        (((Fᶜ.erase w.1).filter fun u =>
          (row w.1 ∩ row u).Nonempty).card =
            m * (q - 3) + (K w.1).card) ∧
        ((Fᶜ.erase w.1).filter fun u =>
          (row w.1 ∩ row u).Nonempty).card ≤ m * (q - 3) + 7 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : V → Finset V := fun w => G.neighborFinset w ∩ S
  let K : V → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w ∩ F
  intro T heven hTcard
  have hprivate :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_privateSupport
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hsum : (∑ w ∈ T, (K w.1).card) ≤ 8 * m := by
    have hcap := hprivate.2.2
    change (∑ w ∈ T, (K w.1).card) ≤ 4 * q at hcap
    calc
      (∑ w ∈ T, (K w.1).card) ≤ 4 * q := hcap
      _ = 8 * m := by omega
  obtain ⟨w, hwT, hwK⟩ :=
    exists_le_seven_of_card_eq_add_four_of_sum_le_eight_mul
      T (fun w => (K w.1).card) m hTcard hsum
  have hdegree :=
    c4Free_binarySquare_pureEndpoint_exterior_rowIntersection_degree
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
      w.1 w.2
  have hdegreeEq : ((Fᶜ.erase w.1).filter fun u =>
      (row w.1 ∩ row u).Nonempty).card =
        m * (q - 3) + (K w.1).card := by
    simpa [F, row, K] using hdegree.1.trans
      (congrArg (fun n => m * (q - 3) + n) hdegree.2)
  refine ⟨w, hwT, hwK, hdegreeEq, ?_⟩
  rw [hdegreeEq]
  omega

end


end Erdos85

#print axioms Erdos85.exists_le_seven_of_card_eq_add_four_of_sum_le_eight_mul
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_exists_lowHoleRow
