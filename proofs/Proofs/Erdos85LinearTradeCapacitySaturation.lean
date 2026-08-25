import Mathlib

/-!
# Equality in a weighted pair-capacity bound

When every negative-positive pair contributes at most its positive weight,
equality in the global capacity bound forces pointwise saturation.  This is
the equality mechanism needed after the strict private-cut inequality becomes
an equality.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Equality in the total weighted pair-capacity bound forces every pair with
positive weight to use its full unit capacity. -/
theorem weighted_pair_capacity_eq_one_of_sum_eq
    {β : Type*} [DecidableEq β]
    (Z P : Finset β) (weight codeg : β → β → ℕ)
    (hcap : ∀ z ∈ Z, ∀ p ∈ P, weight z p * codeg z p ≤ weight z p)
    (hsat : (∑ z ∈ Z, ∑ p ∈ P, weight z p * codeg z p) =
      ∑ z ∈ Z, ∑ p ∈ P, weight z p) :
    ∀ z ∈ Z, ∀ p ∈ P, 0 < weight z p → codeg z p = 1 := by
  intro z hz p hp hweight
  have hrow : (∑ p ∈ P, weight z p * codeg z p) =
      ∑ p ∈ P, weight z p :=
    (Finset.sum_eq_sum_iff_of_le (fun z hz =>
      Finset.sum_le_sum (fun p hp => hcap z hz p hp))).mp hsat z hz
  have hterm : weight z p * codeg z p = weight z p :=
    (Finset.sum_eq_sum_iff_of_le (fun p hp => hcap z hz p hp)).mp hrow p hp
  have hcodegPos : 0 < codeg z p := by
    by_contra hnot
    have hzero : codeg z p = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hzero] at hterm
    omega
  have hcodegLe : codeg z p ≤ 1 := by
    nlinarith [hcap z hz p hp]
  omega

end

end Erdos85

#print axioms Erdos85.weighted_pair_capacity_eq_one_of_sum_eq
