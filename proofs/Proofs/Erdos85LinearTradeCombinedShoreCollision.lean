import Mathlib

/-!
# A combined-shore collision bound for linear trades

A negative/positive trade may be balanced on one point shore and merely
dominated on a second.  If a negative-positive block pair has at most one
common point across both shores, the two collision masses share one global
capacity bound.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Reindex a weighted block collision count by its common points. -/
theorem weighted_commonPoint_collision_reindex
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : β → α → Prop) [DecidableRel Inc]
    (Q : Finset α) (Z P : Finset β) (weight : β → ℕ) :
    (∑ z ∈ Z, ∑ p ∈ P,
      weight p * (Q.filter fun x => Inc z x ∧ Inc p x).card) =
    ∑ x ∈ Q, (Z.filter fun z => Inc z x).card *
      (∑ p ∈ P.filter (fun p => Inc p x), weight p) := by
  classical
  simp only [Finset.card_eq_sum_ones]
  simp_rw [Finset.sum_filter]
  simp only [ite_and]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have hswap :
      (∑ z ∈ Z, ∑ p ∈ P, ∑ x ∈ Q,
          if Inc z x then if Inc p x then weight p else 0 else 0) =
        ∑ x ∈ Q, ∑ p ∈ P, ∑ z ∈ Z,
          if Inc z x then if Inc p x then weight p else 0 else 0 := by
    calc
      _ = ∑ p ∈ P, ∑ z ∈ Z, ∑ x ∈ Q,
          if Inc z x then if Inc p x then weight p else 0 else 0 :=
            Finset.sum_comm
      _ = ∑ p ∈ P, ∑ x ∈ Q, ∑ z ∈ Z,
          if Inc z x then if Inc p x then weight p else 0 else 0 := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact Finset.sum_comm
      _ = ∑ x ∈ Q, ∑ p ∈ P, ∑ z ∈ Z,
          if Inc z x then if Inc p x then weight p else 0 else 0 :=
            Finset.sum_comm
  simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases hzx : Inc z x <;> by_cases hpx : Inc p x <;>
    simp [hzx, hpx]

/-- Combined-shore capacity bound.  The `U`-shore is exactly balanced, the
`X`-shore has at least as many negative incidences as weighted positive
incidences, and each negative-positive pair has total codegree at most one. -/
theorem linear_trade_combinedShore_collision_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : β → α → Prop) [DecidableRel Inc]
    (U X : Finset α) (Z P : Finset β)
    (weight : β → ℕ) (m : ℕ)
    (hrow : ∀ z ∈ Z, (U.filter fun u => Inc z u).card = m)
    (hUbalance : ∀ u ∈ U,
      (Z.filter fun z => Inc z u).card =
        ∑ p ∈ P.filter (fun p => Inc p u), weight p)
    (hXdom : ∀ x ∈ X,
      (∑ p ∈ P.filter (fun p => Inc p x), weight p) ≤
        (Z.filter fun z => Inc z x).card)
    (hpair : ∀ z ∈ Z, ∀ p ∈ P,
      weight p *
          ((U.filter fun u => Inc z u ∧ Inc p u).card +
            (X.filter fun x => Inc z x ∧ Inc p x).card) ≤ weight p)
    (hweight : ∑ p ∈ P, weight p = Z.card) :
    m * Z.card +
        (∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p) ≤
      Z.card * Z.card := by
  classical
  let CU := ∑ z ∈ Z, ∑ p ∈ P,
    weight p * (U.filter fun u => Inc z u ∧ Inc p u).card
  let CX := ∑ z ∈ Z, ∑ p ∈ P,
    weight p * (X.filter fun x => Inc z x ∧ Inc p x).card
  have hCUreindex : CU = ∑ u ∈ U,
      (Z.filter fun z => Inc z u).card *
        (∑ p ∈ P.filter (fun p => Inc p u), weight p) := by
    exact weighted_commonPoint_collision_reindex Inc U Z P weight
  have hCXreindex : CX = ∑ x ∈ X,
      (Z.filter fun z => Inc z x).card *
        (∑ p ∈ P.filter (fun p => Inc p x), weight p) := by
    exact weighted_commonPoint_collision_reindex Inc X Z P weight
  have hCUlower : m * Z.card ≤ CU := by
    rw [hCUreindex]
    calc
      m * Z.card = ∑ u ∈ U, (Z.filter fun z => Inc z u).card := by
        calc
          m * Z.card = Z.card * m := Nat.mul_comm _ _
          _ = ∑ z ∈ Z, (U.filter fun u => Inc z u).card := by
            symm
            exact Finset.sum_const_nat hrow
          _ = ∑ u ∈ U, (Z.filter fun z => Inc z u).card := by
            simp only [Finset.card_eq_sum_ones]
            simp_rw [Finset.sum_filter]
            exact Finset.sum_comm
      _ ≤ ∑ u ∈ U, (Z.filter fun z => Inc z u).card *
          (∑ p ∈ P.filter (fun p => Inc p u), weight p) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [← hUbalance u hu]
        exact Nat.le_mul_self _
  have hCXlower :
      (∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p) ≤ CX := by
    rw [hCXreindex]
    apply Finset.sum_le_sum
    intro x hx
    let a := (Z.filter fun z => Inc z x).card
    let b := ∑ p ∈ P.filter (fun p => Inc p x), weight p
    have hba : b ≤ a := hXdom x hx
    by_cases hb : b = 0
    · simp [b, hb]
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
      calc
        b ≤ b * b := Nat.le_mul_of_pos_left b hbpos
        _ ≤ a * b := Nat.mul_le_mul_right b hba
  have hupper : CU + CX ≤ Z.card * Z.card := by
    calc
      CU + CX = ∑ z ∈ Z, ∑ p ∈ P,
          weight p *
            ((U.filter fun u => Inc z u ∧ Inc p u).card +
              (X.filter fun x => Inc z x ∧ Inc p x).card) := by
        simp [CU, CX, Nat.mul_add, Finset.sum_add_distrib]
      _ ≤ ∑ z ∈ Z, ∑ p ∈ P, weight p := by
        apply Finset.sum_le_sum
        intro z hz
        apply Finset.sum_le_sum
        intro p hp
        exact hpair z hz p hp
      _ = Z.card * Z.card := by
        rw [Finset.sum_const_nat (fun _ _ => hweight)]
  omega

end

end Erdos85

#print axioms Erdos85.weighted_commonPoint_collision_reindex
#print axioms Erdos85.linear_trade_combinedShore_collision_le
