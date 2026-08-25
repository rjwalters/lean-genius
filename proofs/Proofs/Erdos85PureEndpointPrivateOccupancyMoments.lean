import Proofs.Erdos85LinearTradeCombinedShoreCollision

/-!
# Aggregate private-occupancy bookkeeping

This isolates the final double-counting step used by the pure-endpoint
strict-cut gap.  Pointwise, positive row load plus defect equals zero-row
load on the pair-point shore.  Globally, zero rows have constant size and
positive rows have at most `m - 2` pair points.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Aggregate a pointwise zero/positive load identity over the pair-point
shore.  Besides the exact moment identity, the positive-row capacity gives
the energy lower bound `2|Z| ≤ s`. -/
theorem privateOccupancy_pairShore_moment_and_two_mul_zero_le
    {Point Row : Type*} [DecidableEq Point] [DecidableEq Row]
    (Inc : Row → Point → Prop) [DecidableRel Inc]
    (X : Finset Point) (Z H : Finset Row)
    (weight : Row → ℕ) (defect : Point → ℕ) (m s : ℕ)
    (hm : 2 ≤ m)
    (hlocal : ∀ x ∈ X,
      (∑ b ∈ H.filter (fun b => Inc b x), weight b) + defect x =
        (Z.filter fun z => Inc z x).card)
    (hZrow : ∀ z ∈ Z, (X.filter fun x => Inc z x).card = m)
    (hHrow : ∀ b ∈ H, (X.filter fun x => Inc b x).card ≤ m - 2)
    (hdefect : ∑ x ∈ X, defect x = s)
    (hweight : ∑ b ∈ H, weight b = Z.card) :
    (∑ x ∈ X, ∑ b ∈ H.filter (fun b => Inc b x), weight b) + s =
        m * Z.card ∧
      2 * Z.card ≤ s := by
  classical
  have hloadReindex :
      (∑ x ∈ X, ∑ b ∈ H.filter (fun b => Inc b x), weight b) =
        ∑ b ∈ H, weight b * (X.filter fun x => Inc b x).card := by
    simp_rw [Finset.sum_filter]
    have hswap :
        (∑ x ∈ X, ∑ b ∈ H, if Inc b x then weight b else 0) =
          ∑ b ∈ H, ∑ x ∈ X, if Inc b x then weight b else 0 :=
      Finset.sum_comm
    rw [hswap]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hbx : Inc b x <;> simp [hbx]
  have hzeroReindex :
      (∑ x ∈ X, (Z.filter fun z => Inc z x).card) = m * Z.card := by
    calc
      _ = ∑ z ∈ Z, (X.filter fun x => Inc z x).card := by
        simp only [Finset.card_eq_sum_ones]
        simp_rw [Finset.sum_filter]
        exact Finset.sum_comm
      _ = ∑ _z ∈ Z, m := Finset.sum_congr rfl hZrow
      _ = m * Z.card := by simp [Nat.mul_comm]
  have hexact :
      (∑ x ∈ X, ∑ b ∈ H.filter (fun b => Inc b x), weight b) + s =
        m * Z.card := by
    rw [← hdefect, ← Finset.sum_add_distrib]
    calc
      _ = ∑ x ∈ X, (Z.filter fun z => Inc z x).card :=
        Finset.sum_congr rfl hlocal
      _ = m * Z.card := hzeroReindex
  have hloadUpper :
      (∑ x ∈ X, ∑ b ∈ H.filter (fun b => Inc b x), weight b) ≤
        (m - 2) * Z.card := by
    rw [hloadReindex, ← hweight]
    calc
      _ ≤ ∑ b ∈ H, weight b * (m - 2) := by
        apply Finset.sum_le_sum
        intro b hb
        exact Nat.mul_le_mul_left (weight b) (hHrow b hb)
      _ = (m - 2) * ∑ b ∈ H, weight b := by
        simp [Finset.mul_sum, Nat.mul_comm]
  refine ⟨hexact, ?_⟩
  have hmSplit :
      (m - 2) * Z.card + 2 * Z.card = m * Z.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hm]
  omega

end


end Erdos85

#print axioms Erdos85.privateOccupancy_pairShore_moment_and_two_mul_zero_le
