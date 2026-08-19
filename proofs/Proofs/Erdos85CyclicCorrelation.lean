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
    { toFun := fun p => ((p.2 - p.1.2, p.1.2), p.1.2 + p.1.1)
      invFun := fun p => ((p.2 - p.1.2, p.1.2), p.1.2 + p.1.1)
      left_inv := by
        rintro ⟨⟨r, x⟩, y⟩
        simp
      right_inv := by
        rintro ⟨⟨d, x⟩, y⟩
        simp }
  have hlhs :
      (∑ r : ZMod n, (∑ x : ZMod n, f x * g (x + r)) ^ 2) =
        ∑ r : ZMod n, ∑ x : ZMod n, ∑ y : ZMod n,
          (f x * g (x + r)) * (f y * g (y + r)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  have hrhs :
      (∑ d : ZMod n,
          (∑ x : ZMod n, f x * f (x + d)) *
            ∑ y : ZMod n, g y * g (y + d)) =
        ∑ d : ZMod n, ∑ x : ZMod n, ∑ y : ZMod n,
          (f x * f (x + d)) * (g y * g (y + d)) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  rw [hlhs, hrhs]
  conv_lhs => rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  conv_rhs => rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let rhsTerm : (ZMod n × ZMod n) × ZMod n → ℕ := fun p =>
    (f p.1.2 * f (p.1.2 + p.1.1)) * (g p.2 * g (p.2 + p.1.1))
  calc
    _ = ∑ p, rhsTerm (e p) := by
      apply Finset.sum_congr rfl
      rintro ⟨⟨r, x⟩, y⟩ _
      change (f x * g (x + r)) * (f y * g (y + r)) =
        rhsTerm ((y - x, x), x + r)
      simp only [rhsTerm, add_comm x, sub_add_cancel, add_assoc]
      ac_rfl
    _ = ∑ p, rhsTerm p := by simpa [rhsTerm] using Equiv.sum_comp e rhsTerm

end Erdos85

#print axioms Erdos85.sum_cyclicCorrelation_eq_mul_sum
#print axioms Erdos85.sum_sq_cyclicCorrelation_eq_sum_mul_autocorrelation
