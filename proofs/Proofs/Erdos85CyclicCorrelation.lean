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

set_option maxHeartbeats 3000000 in
/-- The second moment of cyclic correlation is the product pairing of the
two cyclic autocorrelations.  This is the additive-energy identity behind a
variance attack on the three-owner obstruction. -/
theorem sum_sq_cyclicCorrelation_eq_sum_mul_autocorrelation
    (n : ℕ) [NeZero n] (f g : ZMod n → ℕ) :
    (∑ r : ZMod n, (∑ x : ZMod n, f x * g (x + r)) ^ 2) =
      ∑ d : ZMod n,
        (∑ x : ZMod n, f x * f (x + d)) *
          ∑ y : ZMod n, g y * g (y + d) := by
  let e : (ZMod n × ZMod n) × ZMod n ≃ (ZMod n × ZMod n) × ZMod n :=
    { toFun := fun p => ((p.1.2 - p.2, p.2 + p.1.1), p.2)
      invFun := fun p => ((p.1.2 - p.2, p.2 + p.1.1), p.2)
      left_inv := by
        rintro ⟨⟨r, x⟩, y⟩
        simp [sub_eq_add_neg, add_assoc]
      right_inv := by
        rintro ⟨⟨d, x⟩, y⟩
        simp [sub_eq_add_neg, add_assoc] }
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  repeat rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv e
  rintro ⟨⟨r, x⟩, y⟩
  simp only [e, sub_add_cancel, add_sub_cancel_right, add_sub_cancel_left,
    add_assoc, add_comm, add_left_comm]
  ac_rfl

end Erdos85

#print axioms Erdos85.sum_cyclicCorrelation_eq_mul_sum
#print axioms Erdos85.sum_sq_cyclicCorrelation_eq_sum_mul_autocorrelation
