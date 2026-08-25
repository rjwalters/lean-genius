import Mathlib

/-!
# Local degree rigidity in an equality trade

The collision proof uses two elementary lower bounds.  Equality in those
bounds forces the corresponding point degrees to be zero-one.  These lemmas
isolate that arithmetic for equality-grid consumers.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- If a finite sum of squares equals the first moment, every natural-valued
entry is at most one. -/
theorem le_one_of_sum_sq_eq_sum
    {α : Type*} [DecidableEq α] (U : Finset α) (a : α → ℕ)
    (hsum : (∑ u ∈ U, (a u) ^ 2) = ∑ u ∈ U, a u) :
    ∀ u ∈ U, a u ≤ 1 := by
  have hpoint : ∀ u ∈ U, a u ≤ (a u) ^ 2 := by
    intro u _hu
    cases ha : a u with
    | zero => simp
    | succ n =>
        simpa [ha, pow_two] using
          (Nat.le_mul_of_pos_left (n + 1) (Nat.succ_pos n))
  intro u hu
  have heq : (a u) ^ 2 = a u :=
    ((Finset.sum_eq_sum_iff_of_le hpoint).mp hsum.symm u hu).symm
  nlinarith

/-- If `b` is pointwise dominated by `a` and the collision sum `a*b`
attains its first-moment lower bound, every point carrying positive `b`-mass
has both degrees equal to one. -/
theorem dominated_collision_eq_imp_eq_one
    {α : Type*} [DecidableEq α] (X : Finset α) (a b : α → ℕ)
    (hdom : ∀ x ∈ X, b x ≤ a x)
    (hsum : (∑ x ∈ X, a x * b x) = ∑ x ∈ X, b x) :
    ∀ x ∈ X, 0 < b x → a x = 1 ∧ b x = 1 := by
  have hpoint : ∀ x ∈ X, b x ≤ a x * b x := by
    intro x hx
    by_cases hb : b x = 0
    · simp [hb]
    · have hbpos : 0 < b x := Nat.pos_of_ne_zero hb
      have hapos : 0 < a x := lt_of_lt_of_le hbpos (hdom x hx)
      calc
        b x = 1 * b x := by simp
        _ ≤ a x * b x := Nat.mul_le_mul_right (b x) hapos
  intro x hx hbpos
  have heq : a x * b x = b x :=
    ((Finset.sum_eq_sum_iff_of_le hpoint).mp hsum.symm x hx).symm
  have ha : a x = 1 := by nlinarith
  have hbLe : b x ≤ 1 := by simpa [ha] using hdom x hx
  exact ⟨ha, by omega⟩

end


end Erdos85

#print axioms Erdos85.le_one_of_sum_sq_eq_sum
#print axioms Erdos85.dominated_collision_eq_imp_eq_one
