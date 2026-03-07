/-
  Aristotle targets for Binomial Theorem OQ01
  Routine supporting lemmas for automated proof search.
  See BinomialTheoremOQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (newton_generalized_binomial)
  - Known results likely in Mathlib (monotonicity, bounds, etc.)
  - Clean theorem statements with no definition sorries
  - No axioms (convert to theorem ... := by sorry instead)
-/
import Mathlib

open Real Finset

noncomputable def genBinom (α : ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k, (α - i)) / (Nat.factorial k : ℝ)

namespace BinomialTheoremOQ01Aristotle

/-- C(alpha, 0) = 1. -/
theorem genBinom_zero (α : ℝ) : genBinom α 0 = 1 := by
  simp [genBinom]

/-- C(alpha, 1) = alpha. -/
theorem genBinom_one (α : ℝ) : genBinom α 1 = α := by
  simp [genBinom, Finset.prod_range_succ]

/-- Recurrence: C(alpha, k+1) = C(alpha, k) * (alpha - k) / (k + 1). -/
theorem genBinom_succ (α : ℝ) (k : ℕ) :
    genBinom α (k + 1) = genBinom α k * ((α - k) / (k + 1)) := by
  simp only [genBinom, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
             Nat.cast_one]
  have hk1 : (Nat.factorial k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk2 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hk1, hk2]

/-- C(n, k) = 0 for natural n when k > n. -/
theorem genBinom_nat_zero_of_gt (n k : ℕ) (hk : n < k) : genBinom (n : ℝ) k = 0 := by
  simp only [genBinom]
  apply div_eq_zero_iff.mpr
  left
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hk)
  push_cast
  ring

/-- C(-1, k) = (-1)^k. -/
theorem genBinom_neg_one (k : ℕ) : genBinom (-1 : ℝ) k = (-1) ^ k := by
  induction k with
  | zero => simp [genBinom]
  | succ k ih =>
    rw [genBinom_succ, ih, pow_succ]
    have hk2 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- C(n, k) = Nat.choose n k for natural n and k ≤ n. -/
theorem genBinom_nat_eq_choose (n k : ℕ) (hkn : k ≤ n) :
    genBinom (n : ℝ) k = Nat.choose n k := by
  simp only [genBinom]
  have prod_eq : ∏ i ∈ Finset.range k, ((n : ℝ) - ↑i) = ↑(n.descFactorial k) := by
    conv_rhs => rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt ((Finset.mem_range.mp hi).trans_le hkn)
    exact (Nat.cast_sub hin).symm
  rw [prod_eq, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hkf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp [hkf]

/-- Derivative recurrence: (k+1) * C(alpha, k+1) = C(alpha, k) * (alpha - k). -/
theorem genBinom_recurrence_deriv (α : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * genBinom α (k + 1) = genBinom α k * (α - k) := by
  rw [genBinom_succ]
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hk1]

/-- ODE coefficient identity: (k+1)*C(alpha,k+1) + k*C(alpha,k) = alpha*C(alpha,k). -/
theorem genBinom_ode_coeff (α : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * genBinom α (k + 1) + k * genBinom α k = α * genBinom α k := by
  rw [genBinom_recurrence_deriv]
  ring

/-- The standard binomial theorem: (1+x)^n = finite sum for natural n. -/
theorem standard_binomial (n : ℕ) (x : ℝ) :
    (1 + x) ^ n = ∑ k ∈ Finset.range (n + 1), genBinom (n : ℝ) k * x ^ k := by
  rw [add_comm 1 x, add_pow x (1 : ℝ) n]
  apply Finset.sum_congr rfl
  intro m hm
  have hm_le : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  simp only [one_pow, mul_one]
  rw [← genBinom_nat_eq_choose n m hm_le]
  ring

end BinomialTheoremOQ01Aristotle
