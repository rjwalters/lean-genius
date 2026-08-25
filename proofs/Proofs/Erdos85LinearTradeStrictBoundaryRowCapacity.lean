import Mathlib

/-!
# Positive-row capacity at the strict boundary

At equality in the private-cut moment, the weighted positive rows attain
their common point-cap.  Hence every row carrying positive weight attains the
cap individually.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Equality in a weighted row-capacity sum forces every positive-weight row
to attain the cap. -/
theorem weighted_row_capacity_eq_of_sum_eq
    {β : Type*} [DecidableEq β]
    (P : Finset β) (weight load : β → ℕ) (cap mass : ℕ)
    (hcap : ∀ p ∈ P, load p ≤ cap)
    (hweight : ∑ p ∈ P, weight p = mass)
    (hsum : ∑ p ∈ P, weight p * load p = cap * mass) :
    ∀ p ∈ P, 0 < weight p → load p = cap := by
  have hterm : ∀ p ∈ P, weight p * load p ≤ weight p * cap := by
    intro p hp
    exact Nat.mul_le_mul_left (weight p) (hcap p hp)
  have hsumCap : (∑ p ∈ P, weight p * cap) = cap * mass := by
    calc
      _ = cap * ∑ p ∈ P, weight p := by
        simp [Finset.mul_sum, Nat.mul_comm]
      _ = cap * mass := by rw [hweight]
  intro p hp hpos
  have heq : weight p * load p = weight p * cap :=
    (Finset.sum_eq_sum_iff_of_le hterm).mp
      (hsum.trans hsumCap.symm) p hp
  nlinarith

end


end Erdos85

#print axioms Erdos85.weighted_row_capacity_eq_of_sum_eq
