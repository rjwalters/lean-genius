/-!
# Erdős Problem #493: Product Minus Sum Representation

Does there exist k such that every sufficiently large integer n
can be written as ∏ aᵢ - ∑ aᵢ for some a₁,...,aₖ ≥ 2?

Yes, with k = 2: for any integer n,
  n = 2·(n+2) - (2 + (n+2)) = 2n + 4 - n - 4 = n.

Status: SOLVED (affirmative, k = 2)

Reference: https://erdosproblems.com/493
Source: [Er61] (attributed to Schinzel)
-/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
## Part I: Product Minus Sum Representation
-/

namespace Erdos493

/-- An integer n has a (k=2) product-minus-sum representation if
    n = a * b - (a + b) for some a, b ≥ 2. -/
def HasProdMinusSum2 (n : ℤ) : Prop :=
  ∃ a b : ℤ, a ≥ 2 ∧ b ≥ 2 ∧ n = a * b - (a + b)

/-- General k-representation: n = ∏ aᵢ - ∑ aᵢ for aᵢ ≥ 2. -/
def HasProdMinusSumK (n : ℤ) (k : ℕ) : Prop :=
  ∃ (as : Fin k → ℤ), (∀ i, as i ≥ 2) ∧
    n = (∏ i, as i) - (∑ i, as i)

/-!
## Part II: The Solution (k = 2)
-/

/-- Key identity: for any integer n, choosing a = 2 and b = n + 2 gives
    2 * (n + 2) - (2 + (n + 2)) = 2n + 4 - n - 4 = n.
    We need b = n + 2 ≥ 2, i.e., n ≥ 0. -/
theorem prod_minus_sum_identity (n : ℤ) : 2 * (n + 2) - (2 + (n + 2)) = n := by
  ring

/-- Every non-negative integer has a product-minus-sum representation with k = 2. -/
theorem erdos_493_nonneg (n : ℤ) (hn : n ≥ 0) : HasProdMinusSum2 n := by
  refine ⟨2, n + 2, le_refl 2, ?_, ?_⟩
  · linarith
  · ring

/-!
## Part III: Negative Integers
-/

/-- For negative integers, we can use a = 2, b = 2 to get 2*2 - (2+2) = 0,
    or use larger values. Specifically, a = 2, b = n + 2 works when n + 2 ≥ 2,
    i.e., n ≥ 0. For n < 0, we use a = -n + 2, b = 2 giving
    2(-n+2) - ((-n+2)+2) = -2n+4-(-n+4) = -2n+4+n-4 = -n.
    Actually, we need aᵢ ≥ 2 as integers (not necessarily positive).
    But the problem states aᵢ ≥ 2, so we handle n ≥ 0. -/

/-- For all sufficiently large n (namely n ≥ 0), the representation exists. -/
theorem erdos_493_sufficiently_large :
    ∃ N₀ : ℤ, ∀ n : ℤ, n ≥ N₀ → HasProdMinusSum2 n :=
  ⟨0, fun n hn => erdos_493_nonneg n hn⟩

/-!
## Part IV: The Main Theorem
-/

/-- Erdős Problem #493: There exists k such that every sufficiently large
    integer has a product-minus-sum representation. In fact, k = 2 works. -/
theorem erdos_493 :
    ∃ (k : ℕ), ∃ N₀ : ℤ, ∀ n : ℤ, n ≥ N₀ →
      HasProdMinusSumK n k :=
  ⟨2, 0, fun n hn => by
    refine ⟨![2, n + 2], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith
    · simp [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring⟩

/-!
## Part V: Explicit Examples
-/

/-- Example: 0 = 2 * 2 - (2 + 2). -/
example : HasProdMinusSum2 0 := ⟨2, 2, le_refl 2, le_refl 2, by ring⟩

/-- Example: 1 = 2 * 3 - (2 + 3). -/
example : HasProdMinusSum2 1 := ⟨2, 3, le_refl 2, by norm_num, by ring⟩

/-- Example: 10 = 2 * 12 - (2 + 12). -/
example : HasProdMinusSum2 10 := ⟨2, 12, le_refl 2, by norm_num, by ring⟩

/-!
## Part VI: Summary

- The product-minus-sum representation exists for k = 2.
- For any n ≥ 0, take a = 2, b = n + 2.
- The key identity: 2(n+2) - (2 + (n+2)) = n.
- Problem SOLVED (affirmative).
-/

/-- The statement is well-defined. -/
theorem erdos_493_statement :
    (∃ (k : ℕ), ∃ N₀ : ℤ, ∀ n : ℤ, n ≥ N₀ → HasProdMinusSumK n k) ↔
    (∃ (k : ℕ), ∃ N₀ : ℤ, ∀ n : ℤ, n ≥ N₀ → HasProdMinusSumK n k) := by simp

/-- The problem is SOLVED. -/
theorem erdos_493_status : True := trivial

end Erdos493
