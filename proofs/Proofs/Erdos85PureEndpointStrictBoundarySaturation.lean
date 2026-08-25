import Proofs.Erdos85LinearTradeCapacitySaturation
import Proofs.Erdos85LinearTradeCombinedShoreCollision
import Proofs.Erdos85LinearTradeEqualityDegrees

/-!
# Pointwise saturation at equality in the combined-shore bound

The strict private-cut boundary makes the lower and upper sides of the
combined-shore collision estimate equal.  This generic equality companion
turns that aggregate equality into the pointwise statement that every
negative/positive row pair of positive weight has exactly one common point
on the two shores.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Equality in the combined-shore capacity bound forces every positive-weight
negative/positive row pair to use its unique available common point. -/
theorem linear_trade_combinedShore_rigidity_of_capacity_eq
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
    (hweight : ∑ p ∈ P, weight p = Z.card)
    (heq : m * Z.card +
        (∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p) =
      Z.card * Z.card) :
    (∀ z ∈ Z, ∀ p ∈ P, 0 < weight p →
      (U.filter fun u => Inc z u ∧ Inc p u).card +
        (X.filter fun x => Inc z x ∧ Inc p x).card = 1) ∧
    (∀ u ∈ U, (Z.filter fun z => Inc z u).card ≤ 1) ∧
    (∀ x ∈ X, 0 < (∑ p ∈ P.filter (fun p => Inc p x), weight p) →
      (Z.filter fun z => Inc z x).card = 1 ∧
        (∑ p ∈ P.filter (fun p => Inc p x), weight p) = 1) := by
  classical
  let codeg : β → β → ℕ := fun z p =>
    (U.filter fun u => Inc z u ∧ Inc p u).card +
      (X.filter fun x => Inc z x ∧ Inc p x).card
  let collision := ∑ z ∈ Z, ∑ p ∈ P, weight p * codeg z p
  have hcollisionUpper : collision ≤ Z.card * Z.card := by
    calc
      collision ≤ ∑ z ∈ Z, ∑ p ∈ P, weight p := by
        apply Finset.sum_le_sum
        intro z hz
        apply Finset.sum_le_sum
        intro p hp
        exact hpair z hz p hp
      _ = Z.card * Z.card := by
        rw [Finset.sum_const_nat (fun _ _ => hweight)]
  have hUlower : m * Z.card ≤
      ∑ z ∈ Z, ∑ p ∈ P,
        weight p * (U.filter fun u => Inc z u ∧ Inc p u).card := by
    rw [weighted_commonPoint_collision_reindex]
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
  have hXlower :
      (∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p) ≤
        ∑ z ∈ Z, ∑ p ∈ P,
          weight p * (X.filter fun x => Inc z x ∧ Inc p x).card := by
    rw [weighted_commonPoint_collision_reindex]
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
  have hcollisionLower : Z.card * Z.card ≤ collision := by
    rw [← heq]
    calc
      m * Z.card +
          (∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p) ≤
          (∑ z ∈ Z, ∑ p ∈ P,
            weight p * (U.filter fun u => Inc z u ∧ Inc p u).card) +
          ∑ z ∈ Z, ∑ p ∈ P,
            weight p * (X.filter fun x => Inc z x ∧ Inc p x).card :=
        Nat.add_le_add hUlower hXlower
      _ = collision := by
        simp [collision, codeg, Nat.mul_add, Finset.sum_add_distrib]
  have hcollisionEq : collision = Z.card * Z.card :=
    Nat.le_antisymm hcollisionUpper hcollisionLower
  have hsat : collision = ∑ z ∈ Z, ∑ p ∈ P, weight p := by
    rw [hcollisionEq, Finset.sum_const_nat (fun _ _ => hweight)]
  have hparts :
      (∑ z ∈ Z, ∑ p ∈ P,
        weight p * (U.filter fun u => Inc z u ∧ Inc p u).card) +
      (∑ z ∈ Z, ∑ p ∈ P,
        weight p * (X.filter fun x => Inc z x ∧ Inc p x).card) = collision := by
    simp [collision, codeg, Nat.mul_add, Finset.sum_add_distrib]
  let load := ∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p
  have hUeq : m * Z.card =
      ∑ z ∈ Z, ∑ p ∈ P,
        weight p * (U.filter fun u => Inc z u ∧ Inc p u).card := by
    change m * Z.card + load = Z.card * Z.card at heq
    omega
  have hXeq : load =
      ∑ z ∈ Z, ∑ p ∈ P,
        weight p * (X.filter fun x => Inc z x ∧ Inc p x).card := by
    change m * Z.card + load = Z.card * Z.card at heq
    omega
  have hUfirst : m * Z.card =
      ∑ u ∈ U, (Z.filter fun z => Inc z u).card := by
    calc
      m * Z.card = Z.card * m := Nat.mul_comm _ _
      _ = ∑ z ∈ Z, (U.filter fun u => Inc z u).card := by
        symm
        exact Finset.sum_const_nat hrow
      _ = ∑ u ∈ U, (Z.filter fun z => Inc z u).card := by
        simp only [Finset.card_eq_sum_ones]
        simp_rw [Finset.sum_filter]
        exact Finset.sum_comm
  have hUsquares :
      (∑ u ∈ U, ((Z.filter fun z => Inc z u).card) ^ 2) =
        ∑ u ∈ U, (Z.filter fun z => Inc z u).card := by
    calc
      _ = ∑ z ∈ Z, ∑ p ∈ P,
          weight p * (U.filter fun u => Inc z u ∧ Inc p u).card := by
        rw [weighted_commonPoint_collision_reindex]
        apply Finset.sum_congr rfl
        intro u hu
        rw [← hUbalance u hu]
        simp [pow_two]
      _ = m * Z.card := hUeq.symm
      _ = _ := hUfirst
  have hUdegree := le_one_of_sum_sq_eq_sum U
    (fun u => (Z.filter fun z => Inc z u).card) hUsquares
  have hXcollision :
      (∑ x ∈ X, (Z.filter fun z => Inc z x).card *
        (∑ p ∈ P.filter (fun p => Inc p x), weight p)) =
      ∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p := by
    calc
      _ = ∑ z ∈ Z, ∑ p ∈ P,
          weight p * (X.filter fun x => Inc z x ∧ Inc p x).card := by
        rw [weighted_commonPoint_collision_reindex]
      _ = load := hXeq.symm
      _ = _ := rfl
  have hXdegree := dominated_collision_eq_imp_eq_one X
    (fun x => (Z.filter fun z => Inc z x).card)
    (fun x => ∑ p ∈ P.filter (fun p => Inc p x), weight p)
    hXdom hXcollision
  refine ⟨?_, hUdegree, hXdegree⟩
  simpa [collision, codeg] using
    weighted_pair_capacity_eq_one_of_sum_eq Z P
      (fun _ p => weight p) codeg hpair hsat

/-- Compatibility projection retaining the original pointwise pair-saturation
API. -/
theorem linear_trade_combinedShore_codeg_eq_one_of_capacity_eq
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
    (hweight : ∑ p ∈ P, weight p = Z.card)
    (heq : m * Z.card +
        (∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p) =
      Z.card * Z.card) :
    ∀ z ∈ Z, ∀ p ∈ P, 0 < weight p →
      (U.filter fun u => Inc z u ∧ Inc p u).card +
        (X.filter fun x => Inc z x ∧ Inc p x).card = 1 :=
  (linear_trade_combinedShore_rigidity_of_capacity_eq
    Inc U X Z P weight m hrow hUbalance hXdom hpair hweight heq).1

/-- Arithmetic form used at the strict private-cut boundary.  The moment
identity and `|Z| = q - 2` make the combined-shore lower bound equal its
quadratic capacity, so the pointwise saturation conclusion follows. -/
theorem linear_trade_combinedShore_rigidity_of_strictBoundary
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : β → α → Prop) [DecidableRel Inc]
    (U X : Finset α) (Z P : Finset β)
    (weight : β → ℕ) (q m cut : ℕ)
    (hqm : q = 2 * m) (hq : 2 ≤ q)
    (hcut : cut = 2 * q - 4) (hZcard : Z.card = q - 2)
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
    (hweight : ∑ p ∈ P, weight p = Z.card)
    (hmoment :
      (∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p) + cut =
        m * Z.card) :
    (∀ z ∈ Z, ∀ p ∈ P, 0 < weight p →
      (U.filter fun u => Inc z u ∧ Inc p u).card +
        (X.filter fun x => Inc z x ∧ Inc p x).card = 1) ∧
    (∀ u ∈ U, (Z.filter fun z => Inc z u).card ≤ 1) ∧
    (∀ x ∈ X, 0 < (∑ p ∈ P.filter (fun p => Inc p x), weight p) →
      (Z.filter fun z => Inc z x).card = 1 ∧
        (∑ p ∈ P.filter (fun p => Inc p x), weight p) = 1) := by
  have heq : m * Z.card +
        (∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p) =
      Z.card * Z.card := by
    have hpoly : 2 * (m * Z.card) = Z.card * Z.card + cut := by
      rw [hZcard, hcut, hqm]
      have hm : 1 ≤ m := by omega
      have hnorm : 2 * (2 * m) - 4 = 2 * (2 * m - 2) := by omega
      have hsub : 2 * m - 2 = 2 * (m - 1) := by omega
      rw [hnorm, hsub]
      nlinarith [Nat.sub_add_cancel hm]
    omega
  exact linear_trade_combinedShore_rigidity_of_capacity_eq
    Inc U X Z P weight m hrow hUbalance hXdom hpair hweight heq

/-- Compatibility projection retaining the original strict-boundary pair
saturation API. -/
theorem linear_trade_combinedShore_codeg_eq_one_of_strictBoundary
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : β → α → Prop) [DecidableRel Inc]
    (U X : Finset α) (Z P : Finset β)
    (weight : β → ℕ) (q m cut : ℕ)
    (hqm : q = 2 * m) (hq : 2 ≤ q)
    (hcut : cut = 2 * q - 4) (hZcard : Z.card = q - 2)
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
    (hweight : ∑ p ∈ P, weight p = Z.card)
    (hmoment :
      (∑ x ∈ X, ∑ p ∈ P.filter (fun p => Inc p x), weight p) + cut =
        m * Z.card) :
    ∀ z ∈ Z, ∀ p ∈ P, 0 < weight p →
      (U.filter fun u => Inc z u ∧ Inc p u).card +
        (X.filter fun x => Inc z x ∧ Inc p x).card = 1 :=
  (linear_trade_combinedShore_rigidity_of_strictBoundary
    Inc U X Z P weight q m cut hqm hq hcut hZcard hrow hUbalance
      hXdom hpair hweight hmoment).1

end

end Erdos85

#print axioms Erdos85.linear_trade_combinedShore_rigidity_of_capacity_eq
#print axioms Erdos85.linear_trade_combinedShore_codeg_eq_one_of_capacity_eq
#print axioms Erdos85.linear_trade_combinedShore_rigidity_of_strictBoundary
#print axioms Erdos85.linear_trade_combinedShore_codeg_eq_one_of_strictBoundary
