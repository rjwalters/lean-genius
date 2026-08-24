import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqualityCutExpansion
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqualityOutsideDegree

/-! # Two-sided cut budget for a minimum exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Double-count a symmetric relation across a finite cut. -/
theorem sum_cross_card_eq_sum_cross_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (R : α → α → Prop) [DecidableRel R] :
    (∑ x ∈ T, (((univ : Finset α) \ T).filter fun y => R x y).card) =
      ∑ y ∈ (univ : Finset α) \ T, (T.filter fun x => R x y).card := by
  simp_rw [card_filter]
  exact (sum_comm :
    (∑ x ∈ T, ∑ y ∈ (univ : Finset α) \ T, if R x y then 1 else 0) =
      ∑ y ∈ (univ : Finset α) \ T, ∑ x ∈ T, if R x y then 1 else 0)

/-- The equality circuit cut has matching explicit lower and upper budgets. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutBudget
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
      T.card = m + 1 →
      let cutMass := ∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
        (row w ∩ row u).Nonempty).card
      (m + 1) * (m * (q - 4)) + q ≤ cutMass ∧
        cutMass ≤ (q * q - q - (m + 1)) * m := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard
  constructor
  · exact c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutExpansion
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  · let R : W → W → Prop := fun w u => (row w ∩ row u).Nonempty
    have hdouble := sum_cross_card_eq_sum_cross_card T R
    have hout :=
      c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_outsideDegree_le
        G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
        T heven hTcard
    have hupper : (∑ u ∈ (univ : Finset W) \ T,
        (T.filter fun w => R w u).card) ≤
        ∑ _u ∈ (univ : Finset W) \ T, m := by
      apply Finset.sum_le_sum
      intro u hu
      have huT : u ∉ T := (mem_sdiff.mp hu).2
      have heq : (T.filter fun w => R w u) =
          T.filter fun w => (row u ∩ row w).Nonempty := by
        ext w
        simp only [mem_filter, R]
        apply and_congr_right
        intro _hwT
        rw [inter_comm]
      rw [heq]
      exact hout u huT
    have hWcard : Fintype.card W = q * q - q := by
      rw [Fintype.card_coe, card_compl]
      have hFcard : F.card = q := by simpa [F] using hCcard
      calc
        Fintype.card V - F.card = q * q - F.card :=
          congrArg (fun n => n - F.card) hcard
        _ = q * q - q := congrArg (fun n => q * q - n) hFcard
    rw [hdouble]
    calc
      (∑ u ∈ (univ : Finset W) \ T, (T.filter fun w => R w u).card) ≤
          ∑ _u ∈ (univ : Finset W) \ T, m := hupper
      _ = ((univ : Finset W) \ T).card * m := by simp
      _ = (q * q - q - (m + 1)) * m := by
        simp [card_sdiff, hWcard, hTcard]

end

end Erdos85

#print axioms Erdos85.sum_cross_card_eq_sum_cross_card
#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutBudget
