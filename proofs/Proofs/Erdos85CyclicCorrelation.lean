import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Cyclic correlation bookkeeping for the three-owner obstruction -/

namespace Erdos85

open scoped BigOperators

/-- Summing a cyclic translate of a function over every shift and every
position gives the product of the two total masses.  This is the exact
first-moment identity behind the third-block overlap census. -/
theorem sum_cyclicCorrelation_eq_mul_sum
    (n : ℕ) [NeZero n] (f g : ZMod n → ℕ) :
    (∑ r : ZMod n, ∑ x : ZMod n, f x * g (x + r)) =
      (∑ x : ZMod n, f x) * ∑ y : ZMod n, g y := by
  rw [Finset.sum_comm]
  have hshift : ∀ x : ZMod n,
      (∑ r : ZMod n, g (x + r)) = ∑ y : ZMod n, g y := by
    intro x
    simpa [add_comm] using (Equiv.sum_comp (Equiv.addRight x) g)
  calc
    (∑ x : ZMod n, ∑ r : ZMod n, f x * g (x + r)) =
        ∑ x : ZMod n, f x * ∑ r : ZMod n, g (x + r) := by
          apply Finset.sum_congr rfl
          intro x _
          simpa using
            (Finset.mul_sum Finset.univ (fun r : ZMod n => g (x + r)) (f x)).symm
    _ = ∑ x : ZMod n, f x * ∑ y : ZMod n, g y := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hshift x]
    _ = (∑ x : ZMod n, f x) * ∑ y : ZMod n, g y := by
          simpa using
            (Finset.sum_mul Finset.univ f (∑ y : ZMod n, g y)).symm

end Erdos85

#print axioms Erdos85.sum_cyclicCorrelation_eq_mul_sum
