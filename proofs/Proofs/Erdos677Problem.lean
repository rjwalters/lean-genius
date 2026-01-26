/-!
# Erdős Problem 677: Distinct LCM of Consecutive Integers

Let `M(n, k) = lcm(n+1, n+2, ..., n+k)` be the least common multiple of `k`
consecutive integers starting at `n+1`.

Is it true that for all `m ≥ n + k`, we have `M(m, k) ≠ M(n, k)`?

The Thue–Siegel theorem implies that for fixed `k`, only finitely many pairs
`(m, n)` with `m ≥ n + k` satisfy `M(m, k) = M(n, k)`.

Erdős knew only two examples with different parameters:
- `M(4, 3) = M(13, 2)` (i.e., `lcm(5,6,7) = lcm(14,15)`)
- `M(3, 4) = M(19, 2)` (i.e., `lcm(4,5,6,7) = lcm(20,21)`)

**Stronger conjecture:** With finitely many exceptions, if `k > 2` and
`m ≥ n + k`, then `∏_{i≤k}(n+i)` and `∏_{i≤k}(m+i)` cannot share the
same set of prime factors.

*Reference:* [erdosproblems.com/677](https://www.erdosproblems.com/677)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

/-! ## LCM of consecutive integers -/

/-- `lcmInterval n k` is `lcm(n+1, n+2, ..., n+k)`, the LCM of `k` consecutive
integers starting at `n+1`. -/
def lcmInterval (n k : ℕ) : ℕ :=
    (Finset.range k).fold Nat.lcm 1 (fun i => n + i + 1)

/-! ## Main conjecture -/

/-- Erdős Problem 677: For all `m ≥ n + k` with `k > 0`, `M(m,k) ≠ M(n,k)`. -/
def ErdosProblem677 : Prop :=
    ∀ (m n k : ℕ), 0 < k → n + k ≤ m → lcmInterval m k ≠ lcmInterval n k

/-! ## Known examples -/

/-- The two known examples where `M(n,k) = M(m,l)` with different parameters:
`lcm(5,6,7) = lcm(14,15) = 210` and `lcm(4,5,6,7) = lcm(20,21) = 420`. -/
axiom lcmInterval_example1 : lcmInterval 4 3 = lcmInterval 13 2
axiom lcmInterval_example2 : lcmInterval 3 4 = lcmInterval 19 2

/-! ## Stronger conjecture: same prime factors -/

/-- `samePrimeFactors a b` holds when `a` and `b` have the same set of prime divisors. -/
def samePrimeFactors (a b : ℕ) : Prop :=
    a.primeFactors = b.primeFactors

/-- The product of `k` consecutive integers starting at `n+1`. -/
def consecutiveProduct (n k : ℕ) : ℕ :=
    (Finset.range k).prod (fun i => n + i + 1)

/-- Stronger conjecture: with finitely many exceptions, if `k > 2` and `m ≥ n + k`,
the consecutive products `∏(n+i)` and `∏(m+i)` do not share the same prime factors. -/
def ErdosProblem677_strong : Prop :=
    ∀ k : ℕ, 2 < k →
      Set.Finite { p : ℕ × ℕ | p.1 + k ≤ p.2 ∧
        samePrimeFactors (consecutiveProduct p.1 k) (consecutiveProduct p.2 k) }

/-! ## Thue–Siegel finiteness -/

/-- Thue–Siegel theorem consequence: for fixed `k`, only finitely many pairs satisfy
`M(m,k) = M(n,k)` with `m ≥ n + k`. -/
axiom thue_siegel_finiteness (k : ℕ) (hk : 0 < k) :
    Set.Finite { p : ℕ × ℕ | p.1 + k ≤ p.2 ∧ lcmInterval p.1 k = lcmInterval p.2 k }

/-! ## Basic properties -/

/-- `lcmInterval n 0 = 1` (empty LCM). -/
theorem lcmInterval_zero (n : ℕ) : lcmInterval n 0 = 1 := by
  simp [lcmInterval]

/-- `lcmInterval n 1 = n + 1`. -/
theorem lcmInterval_one (n : ℕ) : lcmInterval n 1 = n + 1 := by
  simp [lcmInterval, Nat.lcm_one_left]

/-- `consecutiveProduct n 0 = 1` (empty product). -/
theorem consecutiveProduct_zero (n : ℕ) : consecutiveProduct n 0 = 1 := by
  simp [consecutiveProduct]

/-- `consecutiveProduct n 1 = n + 1`. -/
theorem consecutiveProduct_one (n : ℕ) : consecutiveProduct n 1 = n + 1 := by
  simp [consecutiveProduct]

/-- The LCM divides the product of the same range. -/
axiom lcmInterval_dvd_product (n k : ℕ) :
    lcmInterval n k ∣ consecutiveProduct n k

/-- `lcmInterval` is positive when `k > 0`. -/
axiom lcmInterval_pos (n k : ℕ) (hk : 0 < k) : 0 < lcmInterval n k
