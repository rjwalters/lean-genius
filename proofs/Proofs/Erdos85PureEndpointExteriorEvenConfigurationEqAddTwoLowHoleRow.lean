import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddTwoPrivateSupport
import Proofs.Erdos85PureEndpointExteriorRowIntersectionDegree

/-!
# A low-hole row in an `m+2` circuit

The linear total hole-mass cap across `m+2` rows forces one row to have at
most three holes.  The ambient row-intersection formula then gives a concrete
low-degree row in the exterior intersection graph.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- If `m+2` nonnegative weights have total at most `4m`, one is at most
three. -/
theorem exists_le_three_of_card_eq_add_two_of_sum_le_four_mul
    {α : Type*} [DecidableEq α]
    (T : Finset α) (f : α → ℕ) (m : ℕ)
    (hcard : T.card = m + 2)
    (hsum : (∑ x ∈ T, f x) ≤ 4 * m) :
    ∃ x ∈ T, f x ≤ 3 := by
  classical
  by_contra h
  have hall : ∀ x ∈ T, 4 ≤ f x := by
    intro x hx
    have hnle : ¬f x ≤ 3 := by
      intro hle
      exact h ⟨x, hx, hle⟩
    omega
  have hlow : 4 * T.card ≤ ∑ x ∈ T, f x := by
    calc
      4 * T.card = ∑ x ∈ T, 4 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ T, f x := by
        apply Finset.sum_le_sum
        intro x hx
        exact hall x hx
  rw [hcard] at hlow
  omega

set_option maxHeartbeats 800000 in
/-- Every endpoint `m+2` even configuration contains a row with at most
three center holes; its ambient exterior intersection degree is consequently
at most `m(q-3)+3`. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_exists_lowHoleRow
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
      T.card = m + 2 →
      ∃ w ∈ T,
        (K w.1).card ≤ 3 ∧
        (((Fᶜ.erase w.1).filter fun u =>
          (row w.1 ∩ row u).Nonempty).card =
            m * (q - 3) + (K w.1).card) ∧
        ((Fᶜ.erase w.1).filter fun u =>
          (row w.1 ∩ row u).Nonempty).card ≤ m * (q - 3) + 3 := by
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
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_privateSupport
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hsum : (∑ w ∈ T, (K w.1).card) ≤ 4 * m := by
    have hcap := hprivate.2.2
    change (∑ w ∈ T, (K w.1).card) ≤ 2 * q at hcap
    calc
      (∑ w ∈ T, (K w.1).card) ≤ 2 * q := hcap
      _ = 4 * m := by omega
  obtain ⟨w, hwT, hwK⟩ :=
    exists_le_three_of_card_eq_add_two_of_sum_le_four_mul
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

#print axioms Erdos85.exists_le_three_of_card_eq_add_two_of_sum_le_four_mul
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_exists_lowHoleRow
