import Proofs.Erdos85OddSquareOrderNineNearRegularCutArithmetic

/-! # Sharp balanced-square lower bound for 78 ordinary vertices -/

open Finset

namespace Erdos85

set_option maxHeartbeats 2000000

private theorem balancedSquare_point (a x : ℕ) :
    ((2 * a + 1 : ℕ) : ℤ) * x ≤
      (x : ℤ) ^ 2 + (a : ℤ) * (a + 1) := by
  push_cast
  by_cases hle : x ≤ a
  · have hleZ : (x : ℤ) ≤ a := by exact_mod_cast hle
    have hnonneg :
        0 ≤ ((a : ℤ) - x) * ((a : ℤ) + 1 - x) := by
      exact mul_nonneg (by omega) (by omega)
    have hid :
        (x : ℤ) ^ 2 + (a : ℤ) * ((a : ℤ) + 1) -
            (2 * (a : ℤ) + 1) * x =
          ((a : ℤ) - x) * ((a : ℤ) + 1 - x) := by ring
    omega
  · have hge : a + 1 ≤ x := by omega
    have hgeZ : (a : ℤ) + 1 ≤ x := by exact_mod_cast hge
    have hnonneg :
        0 ≤ ((x : ℤ) - a) * ((x : ℤ) - (a + 1)) := by
      exact mul_nonneg (by omega) (by omega)
    have hid :
        (x : ℤ) ^ 2 + (a : ℤ) * ((a : ℤ) + 1) -
            (2 * (a : ℤ) + 1) * x =
          ((x : ℤ) - a) * ((x : ℤ) - ((a : ℤ) + 1)) := by ring
    omega

private theorem balancedSquareSum_le_sum_sq_of_card_78
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 78) (f : ι → ℕ) :
    orderNineBalancedSquareSum (∑ i, f i) ≤ ∑ i, (f i) ^ 2 := by
  let M := ∑ i, f i
  let a := M / 78
  let r := M % 78
  have hM : M = 78 * a + r := by
    dsimp only [a, r]
    omega
  have hr : r < 78 := by
    dsimp only [r]
    omega
  have hpoint : ∀ i : ι,
      ((2 * a + 1 : ℕ) : ℤ) * f i ≤
        (f i : ℤ) ^ 2 + (a : ℤ) * (a + 1) := by
    intro i
    exact balancedSquare_point a (f i)
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hpoint i
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hcard] at hsum
  rw [← Finset.mul_sum] at hsum
  have hgoalZ :
      (orderNineBalancedSquareSum M : ℤ) ≤
        ((∑ i, (f i) ^ 2 : ℕ) : ℤ) := by
    rw [show orderNineBalancedSquareSum M =
        (78 - r) * a ^ 2 + r * (a + 1) ^ 2 by rfl]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hr)]
    push_cast
    have hsumF : (∑ i, (f i : ℤ)) = (M : ℤ) := by simp [M]
    have hsumSq : (∑ i, (f i : ℤ) ^ 2) =
        ((∑ i, f i ^ 2 : ℕ) : ℤ) := by simp
    rw [hsumF, hsumSq] at hsum
    push_cast at hsum
    have hMZ : (M : ℤ) = 78 * (a : ℤ) + r := by exact_mod_cast hM
    have hid :
        ((78 : ℤ) - r) * (a : ℤ) ^ 2 +
            (r : ℤ) * ((a : ℤ) + 1) ^ 2 +
            78 * (a : ℤ) * ((a : ℤ) + 1) =
          (2 * (a : ℤ) + 1) * (M : ℤ) := by
      rw [hMZ]
      ring
    ring_nf at hsum hid ⊢
    linarith
  exact_mod_cast hgoalZ

/-- Among 78 natural numbers with fixed sum, the sum of squares is minimized
by the balanced quotient/remainder distribution. -/
theorem orderNineBalancedSquareSum_le_sum_sq (f : Fin 78 → ℕ) :
    orderNineBalancedSquareSum (∑ i, f i) ≤ ∑ i, (f i) ^ 2 := by
  exact balancedSquareSum_le_sum_sq_of_card_78 (by simp) f

#print axioms orderNineBalancedSquareSum_le_sum_sq

end Erdos85
