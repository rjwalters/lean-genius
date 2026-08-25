import Proofs.Erdos85PureEndpointZeroPrivateRows

/-!
# Equality in the linear uniform trade bound

The equality case of `linear_uniform_trade_negative_card_ge` is rigid: every
negative block meets every positive-weight block in exactly one point of the
ground set.  This is the abstract grid used by the pure-endpoint minimum-cut
terminal.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Equality in the linear-uniform-trade support bound produces a complete
grid of intersections between the negative and positive supports. -/
theorem linear_uniform_trade_eq_card_common_eq_one
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (Inc : β → α → Prop) [DecidableRel Inc]
    (U : Finset α) (Z P : Finset β)
    (weight : β → ℕ) (m : ℕ)
    (hrow : ∀ z ∈ Z, (U.filter fun u => Inc z u).card = m)
    (hbalance : ∀ u ∈ U,
      (Z.filter fun z => Inc z u).card =
        ∑ p ∈ P.filter (fun p => Inc p u), weight p)
    (hlinear : ∀ z ∈ Z, ∀ p ∈ P,
      weight p * (U.filter fun u => Inc z u ∧ Inc p u).card ≤ weight p)
    (hweight : ∑ p ∈ P, weight p = Z.card)
    (heq : m = Z.card) :
    ∀ z ∈ Z, ∀ p ∈ P, 0 < weight p →
      (U.filter fun u => Inc z u ∧ Inc p u).card = 1 := by
  classical
  let C := ∑ z ∈ Z, ∑ p ∈ P,
    weight p * (U.filter fun u => Inc z u ∧ Inc p u).card
  have hCupper : C ≤ ∑ z ∈ Z, ∑ p ∈ P, weight p := by
    apply Finset.sum_le_sum
    intro z hz
    apply Finset.sum_le_sum
    intro p hp
    exact hlinear z hz p hp
  have hCreindex : C = ∑ u ∈ U,
      (Z.filter fun z => Inc z u).card *
        (∑ p ∈ P.filter (fun p => Inc p u), weight p) := by
    simp only [C, Finset.card_eq_sum_ones]
    simp_rw [Finset.sum_filter]
    simp only [ite_and]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    have hswap :
        (∑ z ∈ Z, ∑ p ∈ P, ∑ u ∈ U,
            if Inc z u then if Inc p u then weight p else 0 else 0) =
          ∑ u ∈ U, ∑ p ∈ P, ∑ z ∈ Z,
            if Inc z u then if Inc p u then weight p else 0 else 0 := by
      calc
        (∑ z ∈ Z, ∑ p ∈ P, ∑ u ∈ U,
            if Inc z u then if Inc p u then weight p else 0 else 0) =
            ∑ p ∈ P, ∑ z ∈ Z, ∑ u ∈ U,
              if Inc z u then if Inc p u then weight p else 0 else 0 :=
                Finset.sum_comm
        _ = ∑ p ∈ P, ∑ u ∈ U, ∑ z ∈ Z,
              if Inc z u then if Inc p u then weight p else 0 else 0 := by
                apply Finset.sum_congr rfl
                intro p _hp
                exact Finset.sum_comm
        _ = ∑ u ∈ U, ∑ p ∈ P, ∑ z ∈ Z,
              if Inc z u then if Inc p u then weight p else 0 else 0 :=
                Finset.sum_comm
    simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]
    rw [hswap]
    apply Finset.sum_congr rfl
    intro u _hu
    apply Finset.sum_congr rfl
    intro p _hp
    apply Finset.sum_congr rfl
    intro z _hz
    by_cases hzu : Inc z u <;> by_cases hpu : Inc p u <;>
      simp [hzu, hpu]
  have hClower : m * Z.card ≤ C := by
    rw [hCreindex]
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
      _ ≤ ∑ u ∈ U,
          (Z.filter fun z => Inc z u).card *
            (∑ p ∈ P.filter (fun p => Inc p u), weight p) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [← hbalance u hu]
        exact Nat.le_mul_self _
  have hupperValue : (∑ z ∈ Z, ∑ p ∈ P, weight p) = Z.card * Z.card := by
    rw [Finset.sum_const_nat (fun _ _ => hweight)]
  have hCeq : C = ∑ z ∈ Z, ∑ p ∈ P, weight p := by
    apply Nat.le_antisymm hCupper
    rw [hupperValue, ← heq]
    simpa [heq] using hClower
  have hzEq : ∀ z ∈ Z,
      (∑ p ∈ P,
        weight p * (U.filter fun u => Inc z u ∧ Inc p u).card) =
        ∑ p ∈ P, weight p := by
    exact (Finset.sum_eq_sum_iff_of_le (fun z hz =>
      Finset.sum_le_sum fun p hp => hlinear z hz p hp)).mp hCeq
  intro z hz p hp hpPos
  have hpEq := (Finset.sum_eq_sum_iff_of_le
    (fun p hp => hlinear z hz p hp)).mp (hzEq z hz) p hp
  have hmul :
      weight p * (U.filter fun u => Inc z u ∧ Inc p u).card =
        weight p * 1 := by
    simpa using hpEq
  exact Nat.eq_of_mul_eq_mul_left hpPos hmul

end

end Erdos85

#print axioms Erdos85.linear_uniform_trade_eq_card_common_eq_one
