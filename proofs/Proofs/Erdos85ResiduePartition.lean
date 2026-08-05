import Proofs.Erdos85CycleCoverRigidity

/-!
# Residue partitions forced by the second-order square identity

After an unequal defect-cycle block has been identified as a cyclic cover,
the short--long block of

`A² = (d-1)I + J - D`

is an equality of three nonnegative counts with total one.  The contribution
from the short component and the contributions through the two long
components therefore partition the residue classes exactly.  This file
records the arithmetic core independently of any parameter enumeration.
-/

namespace Erdos85

/-- Three nonnegative counts summing to one have exactly one active term. -/
theorem nat_three_sum_eq_one_partition {a b c : ℕ}
    (h : a + b + c = 1) :
    (a = 1 ↔ b = 0 ∧ c = 0) ∧
      (a = 0 ↔ b + c = 1) ∧
      b ≤ 1 ∧ c ≤ 1 ∧ (b = 0 ∨ c = 0) := by
  omega

/-- Functional form of the residue partition.  At every pair `(x,y)`, the
short-component contribution is one exactly when both long-component
contributions vanish; otherwise the latter two contain one unit in total and
cannot both be positive. -/
theorem pointwise_residue_partition
    {X Y : Type*} (short left right : X → Y → ℕ)
    (hsum : ∀ x y, short x y + left x y + right x y = 1) :
    ∀ x y,
      (short x y = 1 ↔ left x y = 0 ∧ right x y = 0) ∧
      (short x y = 0 ↔ left x y + right x y = 1) ∧
      left x y ≤ 1 ∧ right x y ≤ 1 ∧
      (left x y = 0 ∨ right x y = 0) := by
  intro x y
  exact nat_three_sum_eq_one_partition (hsum x y)

/-- Matrix-block specialization.  This is the exact form needed after the
short-to-long blocks have been normalized as cyclic-cover incidence
matrices. -/
theorem matrix_block_residue_partition
    {S L₁ L₂ : Type*}
    [Fintype S] [Fintype L₁] [Fintype L₂]
    [DecidableEq S] [DecidableEq L₁] [DecidableEq L₂]
    (H : Matrix S S ℕ) (P : Matrix S L₁ ℕ)
    (R : Matrix S L₂ ℕ) (B : Matrix L₁ L₁ ℕ)
    (C : Matrix L₂ L₁ ℕ)
    (f : L₁ → S)
    (hcover : ∀ x y, P x y = if x = f y then 1 else 0)
    (hsquare : ∀ x y,
      (H * P) x y + (P * B) x y + (R * C) x y = 1) :
    ∀ x y,
      (H x (f y) = 1 ↔ (P * B) x y = 0 ∧ (R * C) x y = 0) ∧
      (H x (f y) = 0 ↔ (P * B) x y + (R * C) x y = 1) ∧
      (P * B) x y ≤ 1 ∧ (R * C) x y ≤ 1 ∧
      ((P * B) x y = 0 ∨ (R * C) x y = 0) := by
  intro x y
  have hHP : (H * P) x y = H x (f y) := by
    rw [Matrix.mul_apply]
    calc
      (∑ z, H x z * P z y) = ∑ z, H x z * (if z = f y then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [hcover]
      _ = H x (f y) := by simp
  apply nat_three_sum_eq_one_partition
  rw [← hHP]
  exact hsquare x y

end Erdos85
