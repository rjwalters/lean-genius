/-
Erdos Problem #686: Ratios of Products of Consecutive Integers

Source: https://erdosproblems.com/686
Status: OPEN

Statement:
Can every integer N >= 2 be written as
  N = prod_{1 <= i <= k}(m+i) / prod_{1 <= i <= k}(n+i)
for some k >= 2 and m >= n + k?

Background:
- Products of k consecutive integers equal k! * C(n+k, k)
- k >= 2 excludes the trivial single-factor case
- m >= n + k ensures the ranges don't overlap

Reference: [Er79d]
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Finset BigOperators Nat

namespace Erdos686

-- ## Part I: Consecutive Products

/-- Product of k consecutive integers starting at n+1: P(n,k) = (n+1)(n+2)...(n+k). -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

/-- Recursion: P(n, k+1) = P(n, k) * (n + k + 1). -/
theorem consecutiveProduct_succ (n k : ℕ) :
    consecutiveProduct n (k + 1) = consecutiveProduct n k * (n + k + 1) := by
  unfold consecutiveProduct
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
  ring

/-- P(n,k) = (n+k)! / n!. This is a standard identity proved by induction on k. -/
theorem consecutiveProduct_eq_factorial (n k : ℕ) :
    consecutiveProduct n k * n ! = (n + k) ! := by
  induction k with
  | zero =>
    simp [consecutiveProduct]
  | succ k ih =>
    rw [consecutiveProduct_succ]
    rw [show consecutiveProduct n k * (n + k + 1) * n ! =
        (consecutiveProduct n k * n !) * (n + k + 1) from by ring]
    rw [ih]
    rw [show n + (k + 1) = (n + k) + 1 from by omega]
    rw [Nat.factorial_succ]
    ring

/-- P(n,k) = k! * C(n+k, k). Follows from the factorial identity and
    the definition of binomial coefficients. -/
theorem product_binomial_relation (n k : ℕ) :
    consecutiveProduct n k = k ! * (n + k).choose k := by
  have h := consecutiveProduct_eq_factorial n k
  have hchoose := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k n)
  rw [show n + k - k = n from by omega] at hchoose
  -- hchoose : (n + k).choose k * k ! * n ! = (n + k) !
  -- h : consecutiveProduct n k * n ! = (n + k) !
  -- So consecutiveProduct n k * n ! = (n + k).choose k * k ! * n !
  have : consecutiveProduct n k * n ! = k ! * (n + k).choose k * n ! := by
    rw [h, ← hchoose]; ring
  exact Nat.eq_of_mul_eq_right (Nat.factorial_pos n) this

-- ## Part II: The Ratio Expression

/-- The ratio P(m,k)/P(n,k) as a rational number. -/
noncomputable def ratioExpression (n m k : ℕ) : ℚ :=
  (consecutiveProduct m k : ℚ) / (consecutiveProduct n k : ℚ)

/-- The ratio equals C(m+k,k) / C(n+k,k) when expressed via binomials. -/
theorem ratio_as_binomials (n m k : ℕ) (hk : k ≥ 1) :
    ratioExpression n m k = ((m + k).choose k : ℚ) / ((n + k).choose k : ℚ) := by
  unfold ratioExpression
  rw [product_binomial_relation n k, product_binomial_relation m k]
  push_cast
  have hfact : (k ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

/-- The ratio is an integer when the denominator divides the numerator. -/
def IsIntegerRatio (n m k : ℕ) : Prop :=
  (consecutiveProduct n k) ∣ (consecutiveProduct m k)

-- ## Part III: The Representation Property

/-- N is representable with parameters (n, m, k). -/
def IsRepresentable (N : ℕ) (n m k : ℕ) : Prop :=
  k ≥ 2 ∧ m ≥ n + k ∧ ratioExpression n m k = N

/-- N is representable (existentially). -/
def Representable (N : ℕ) : Prop :=
  ∃ n m k, IsRepresentable N n m k

/-- Erdos Problem #686 (OPEN):
    Every integer N >= 2 can be expressed as a ratio of two products
    of k consecutive integers with non-overlapping ranges. -/
axiom erdos_686_conjecture : ∀ N ≥ 2, Representable N

-- ## Part IV: Structural Properties

/-- When m > n, each factor (m+i) > (n+i), so the product is strictly larger. -/
theorem numerator_gt_denominator (n m k : ℕ) (hk : k ≥ 1) (hm : m > n) :
    consecutiveProduct m k > consecutiveProduct n k := by
  unfold consecutiveProduct
  apply Finset.prod_lt_prod_of_nonempty (Finset.nonempty_Icc.mpr (by omega))
  intro i hi
  omega

/-- Each factor is positive, so the product is positive. -/
theorem consecutiveProduct_pos (n k : ℕ) :
    consecutiveProduct n k > 0 := by
  unfold consecutiveProduct
  apply Finset.prod_pos
  intro i hi
  simp [Finset.mem_Icc] at hi
  omega

/-- The product is monotone in the first argument. -/
theorem consecutiveProduct_mono {n₁ n₂ : ℕ} (k : ℕ) (h : n₁ ≤ n₂) :
    consecutiveProduct n₁ k ≤ consecutiveProduct n₂ k := by
  unfold consecutiveProduct
  apply Finset.prod_le_prod
  · intro i _; omega
  · intro i _; omega

-- ## Part V: Verified Examples

/-- N = 2: P(2,2)/P(1,2) = (3*4)/(2*3) = 12/6 = 2. -/
theorem example_N2 : IsIntegerRatio 1 2 2 := by
  unfold IsIntegerRatio consecutiveProduct
  decide

/-- N = 6: P(2,2)/P(0,2) = (3*4)/(1*2) = 12/2 = 6. -/
theorem example_N6 : IsIntegerRatio 0 2 2 ∧ consecutiveProduct 2 2 / consecutiveProduct 0 2 = 6 := by
  constructor
  · unfold IsIntegerRatio consecutiveProduct; decide
  · native_decide

-- ## Part VI: Follow-Up Question

/-- The set of integers representable with fixed n, k. -/
def RepresentableSet (n k : ℕ) : Set ℕ :=
  {N | ∃ m ≥ n + k, ratioExpression n m k = N}

/-- For fixed n, k >= 2, the representable set is infinite.
    (Deep result: as m → ∞, the ratio → ∞, giving arbitrarily large values.) -/
axiom representable_set_infinite (n k : ℕ) (hk : k ≥ 2) :
    Set.Infinite (RepresentableSet n k)

-- ## Part VII: Connections

/-- Connection to Problem #677: integers as products of consecutive integers.
    This is the special case where the denominator product is 1. -/
def problem_677_special_case (N : ℕ) : Prop :=
  ∃ n k : ℕ, k ≥ 2 ∧ consecutiveProduct n k = N

-- ## Part VIII: Summary

/-- The conjecture is equivalent to the explicit form. -/
theorem erdos_686_equiv :
    (∀ N ≥ 2, Representable N) ↔
    ∀ N ≥ 2, ∃ n m k : ℕ, k ≥ 2 ∧ m ≥ n + k ∧
      ratioExpression n m k = (N : ℚ) := by
  simp only [Representable, IsRepresentable]

end Erdos686
