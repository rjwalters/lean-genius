import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# The Binomial Theorem

## What This Proves
The Binomial Theorem: For any elements x, y in a commutative ring and non-negative integer n:

(x + y)^n = ∑_{k=0}^{n} C(n,k) * x^k * y^(n-k)

where C(n,k) = n! / (k!(n-k)!) is the binomial coefficient.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `add_pow` theorem which gives the
  binomial expansion directly.
- **Key Insight:** The expansion arises from choosing which factors contribute x vs y
  when multiplying out (x + y)^n.
- **Proof Techniques Demonstrated:** Ring operations, finite sums, combinatorics.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `add_pow` : The main binomial theorem expansion
- `Nat.choose` : Binomial coefficient definition
- `Nat.add_pow` : Alternate form for natural numbers
- `sum_range_choose` : Sum of binomial coefficients equals 2^n

## Historical Note
The binomial theorem was known to ancient mathematicians in special cases.
Al-Karaji (c. 1000) described the triangle of coefficients, Yang Hui (1261)
published Pascal's triangle in China, and Newton (1665) extended the theorem
to fractional and negative exponents.

This is #44 on Wiedijk's list of 100 theorems.
-/

namespace BinomialTheorem

open Finset BigOperators

/-! ## The Main Theorem

The binomial theorem expresses (x + y)^n as a sum involving binomial coefficients.
Each term corresponds to choosing k factors of x from the n factors. -/

/-- **The Binomial Theorem (Wiedijk #44)**

For any elements x, y in a commutative semiring and natural number n:
(x + y)^n = ∑_{k=0}^{n} C(n,k) * x^k * y^(n-k)

This is one of the most fundamental results in algebra and combinatorics. -/
theorem binomial_theorem {R : Type*} [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ k in range (n + 1), Nat.choose n k * x ^ k * y ^ (n - k) := by
  rw [add_pow]
  congr 1
  ext k
  ring

/-! ## Corollaries

### Sum of Binomial Coefficients

Setting x = y = 1 gives the sum of all binomial coefficients. -/

/-- **Sum of Binomial Coefficients**

The sum of binomial coefficients C(n,0) + C(n,1) + ... + C(n,n) = 2^n.

Proof: Set x = y = 1 in the binomial theorem, giving (1+1)^n = 2^n. -/
theorem sum_binomial_coefficients (n : ℕ) :
    ∑ k in range (n + 1), Nat.choose n k = 2 ^ n :=
  Nat.sum_range_choose n

/-! ### Alternating Sum of Binomial Coefficients

Setting x = 1, y = -1 shows the alternating sum vanishes (for n ≥ 1). -/

/-- **Alternating Sum of Binomial Coefficients**

For n ≥ 1: C(n,0) - C(n,1) + C(n,2) - ... = 0.

Proof: Set x = 1, y = -1 in the binomial theorem, giving (1-1)^n = 0. -/
theorem alternating_sum_binomial (n : ℕ) (hn : 0 < n) :
    ∑ k in range (n + 1), (-1 : ℤ) ^ k * Nat.choose n k = 0 := by
  have h : ∑ m in range (n + 1), (-1 : ℤ) ^ m * ↑(Nat.choose n m) = if n = 0 then 1 else 0 :=
    Int.alternating_sum_range_choose
  simp only [Nat.pos_iff_ne_zero.mp hn, ↓reduceIte] at h
  exact h

/-! ## Pascal's Identity

The recursive relationship between binomial coefficients. -/

/-- **Pascal's Identity**

C(n+1, k+1) = C(n, k) + C(n, k+1) for all n, k.

This is the fundamental recurrence that defines Pascal's triangle. -/
theorem pascal_identity (n k : ℕ) :
    Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
  Nat.choose_succ_succ n k

/-- **Symmetry of Binomial Coefficients**

C(n, k) = C(n, n-k) for k ≤ n.

Choosing k items is the same as choosing which n-k items to leave out. -/
theorem binomial_symmetry (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = Nat.choose n (n - k) :=
  (Nat.choose_symm h).symm

/-- **Binomial Coefficient at 0**

C(n, 0) = 1 for all n. There is exactly one way to choose nothing. -/
theorem binomial_zero (n : ℕ) : Nat.choose n 0 = 1 :=
  Nat.choose_zero_right n

/-- **Binomial Coefficient at n**

C(n, n) = 1 for all n. There is exactly one way to choose everything. -/
theorem binomial_self (n : ℕ) : Nat.choose n n = 1 :=
  Nat.choose_self n

/-! ## Special Cases

Explicit expansions for small exponents. -/

/-- **Binomial Theorem for n = 2**

(x + y)² = x² + 2xy + y² -/
theorem binomial_square {R : Type*} [CommSemiring R] (x y : R) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

/-- **Binomial Theorem for n = 3**

(x + y)³ = x³ + 3x²y + 3xy² + y³ -/
theorem binomial_cube {R : Type*} [CommSemiring R] (x y : R) :
    (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  ring

/-! ## Examples and Verification -/

/-- Verify: (1 + 1)^4 = 16 using binomial expansion -/
example : (1 + 1 : ℕ) ^ 4 = 16 := by native_decide

/-- Verify: C(4,0) + C(4,1) + C(4,2) + C(4,3) + C(4,4) = 16 -/
example : Nat.choose 4 0 + Nat.choose 4 1 + Nat.choose 4 2 +
          Nat.choose 4 3 + Nat.choose 4 4 = 16 := by native_decide

/-- Verify: C(5,2) = 10 -/
example : Nat.choose 5 2 = 10 := by native_decide

/-- Verify: C(10,5) = 252 -/
example : Nat.choose 10 5 = 252 := by native_decide

/-- Verify Pascal's identity: C(5,3) = C(4,2) + C(4,3) -/
example : Nat.choose 5 3 = Nat.choose 4 2 + Nat.choose 4 3 := by native_decide

/-- Verify symmetry: C(6,2) = C(6,4) -/
example : Nat.choose 6 2 = Nat.choose 6 4 := by native_decide

#check binomial_theorem
#check sum_binomial_coefficients
#check alternating_sum_binomial
#check pascal_identity

end BinomialTheorem
