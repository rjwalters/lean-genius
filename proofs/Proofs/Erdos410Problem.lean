/-
Erdős Problem #410: Iterated Sum of Divisors Growth

**Problem Statement (OPEN)**

Let σ₁(n) = σ(n), the sum of divisors function, and σₖ(n) = σ(σₖ₋₁(n)).

Is it true that lim_{k → ∞} σₖ(n)^{1/k} = ∞ for all n ≥ 2?

**Background:**
- σ(n) = sum of all divisors of n (including 1 and n)
- σₖ is the k-th iterate of σ
- We ask about the exponential growth rate of iterates

**Known Results:**
- σ(n) > n for all n > 1 (abundancy)
- The iterates grow, but how fast?
- Related to perfect numbers and aliquot sequences

**Status:** OPEN

**Reference:** [ErGr80], Guy Problem B9, OEIS A007497

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Nat ArithmeticFunction Filter

namespace Erdos410

/-!
# Part 1: The Sum of Divisors Function

σ(n) = sum of all positive divisors of n.
-/

-- The sum of divisors function from Mathlib
-- sigma 1 : ℕ → ℕ gives σ(n)

-- Basic properties
theorem sigma_pos (n : ℕ) (hn : n > 0) : sigma 1 n > 0 := by
  sorry -- σ(n) ≥ 1 + n > 0

theorem sigma_gt_n (n : ℕ) (hn : n > 1) : sigma 1 n > n := by
  sorry -- n has at least divisors 1 and n, so σ(n) ≥ 1 + n > n

-- σ(1) = 1
theorem sigma_one : sigma 1 1 = 1 := by
  sorry

-- σ(p) = p + 1 for prime p
theorem sigma_prime (p : ℕ) (hp : p.Prime) : sigma 1 p = p + 1 := by
  sorry

/-!
# Part 2: Iterated Sum of Divisors

Define σₖ(n) = σ(σ(...σ(n)...)) with k applications.
-/

-- The k-th iterate of σ
noncomputable def sigmaIterate (k n : ℕ) : ℕ :=
  (sigma 1)^[k] n

-- Alternative notation
notation "σ[" k "]" => sigmaIterate k

-- Base case: σ₀(n) = n
theorem sigma_iterate_zero (n : ℕ) : sigmaIterate 0 n = n := by
  simp only [sigmaIterate, Function.iterate_zero_apply]

-- Recursion: σₖ₊₁(n) = σ(σₖ(n))
theorem sigma_iterate_succ (k n : ℕ) :
    sigmaIterate (k + 1) n = sigma 1 (sigmaIterate k n) := by
  simp only [sigmaIterate, Function.iterate_succ_apply']

-- Small examples
theorem sigma_iterate_one (n : ℕ) : sigmaIterate 1 n = sigma 1 n := by
  simp only [sigmaIterate, Function.iterate_one]

/-!
# Part 3: Growth of Iterates

The iterates σₖ(n) grow, but how fast?
-/

-- σₖ(n) is increasing in k for n > 1
theorem sigma_iterate_increasing (n : ℕ) (hn : n > 1) (k : ℕ) :
    sigmaIterate k n < sigmaIterate (k + 1) n := by
  sorry -- Uses σ(m) > m for m > 1

-- Therefore σₖ(n) → ∞ as k → ∞
theorem sigma_iterate_tendsto_infty (n : ℕ) (hn : n > 1) :
    Tendsto (fun k => sigmaIterate k n) atTop atTop := by
  sorry -- Monotone and unbounded

/-!
# Part 4: The Main Conjecture

Does σₖ(n)^{1/k} → ∞?
-/

-- The normalized growth rate
noncomputable def growthRate (n k : ℕ) : ℝ :=
  (sigmaIterate k n : ℝ) ^ (1 / (k : ℝ))

-- The main conjecture
def ErdosConjecture410 : Prop :=
  ∀ n > 1, Tendsto (fun k => growthRate n k) atTop atTop

-- Equivalent formulation: σₖ(n) grows faster than any exponential
theorem conjecture_equiv : ErdosConjecture410 ↔
    ∀ n > 1, ∀ c > 0, ∃ K : ℕ, ∀ k ≥ K, sigmaIterate k n > c^k := by
  sorry

/-!
# Part 5: Bounds on σ

Understanding σ helps understand iterates.
-/

-- Lower bound: σ(n) ≥ n + 1 for n > 1
theorem sigma_lower_bound (n : ℕ) (hn : n > 1) : sigma 1 n ≥ n + 1 := by
  sorry

-- Upper bound: σ(n) ≤ n * H_n approximately (where H_n is harmonic number)
-- More precisely: σ(n) < e^γ * n * log(log n) + c for large n
axiom sigma_upper_bound : ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 3,
    (sigma 1 n : ℝ) < Real.exp 0.5772 * n * Real.log (Real.log n) + c

-- Average behavior: Σ_{d|n} d / n = σ(n) / n
-- On average, σ(n) / n ≈ π²/6
axiom average_sigma : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |(∑ k ∈ Finset.range n, (sigma 1 k : ℝ) / k) / n - Real.pi^2 / 6| < ε

/-!
# Part 6: Special Numbers

Perfect, abundant, and deficient numbers.
-/

-- A number is perfect if σ(n) = 2n
def IsPerfect (n : ℕ) : Prop := sigma 1 n = 2 * n

-- A number is abundant if σ(n) > 2n
def IsAbundant (n : ℕ) : Prop := sigma 1 n > 2 * n

-- A number is deficient if σ(n) < 2n
def IsDeficient (n : ℕ) : Prop := sigma 1 n < 2 * n

-- For perfect n, σ₁(n) = 2n, σ₂(n) = σ(2n), etc.
-- The iterates still grow

-- Known perfect numbers
def perfect_6 : IsPerfect 6 := by sorry
def perfect_28 : IsPerfect 28 := by sorry

/-!
# Part 7: Aliquot Sequences

Related to the aliquot sequence s(n) = σ(n) - n.
-/

-- Aliquot function: s(n) = σ(n) - n (sum of proper divisors)
def aliquot (n : ℕ) : ℕ := sigma 1 n - n

-- σₖ relates to iterated aliquot
-- σ(n) = n + s(n)

-- Aliquot sequence: n → s(n) → s²(n) → ...
-- Can terminate (at 0 or 1), enter cycles, or grow unboundedly

-- The Catalan-Dickson conjecture: all aliquot sequences are bounded or terminate
def CatalanDicksonConjecture : Prop :=
  ∀ n > 0, ∃ k : ℕ, aliquot^[k] n = 0 ∨ ∃ c : ℕ, aliquot^[k] n = c ∧ aliquot c = c

/-!
# Part 8: Explicit Computations

Some explicit values of iterated σ.
-/

-- σ(2) = 1 + 2 = 3
-- σ(3) = 1 + 3 = 4
-- σ(4) = 1 + 2 + 4 = 7
-- σ(6) = 1 + 2 + 3 + 6 = 12

-- For n = 2:
-- σ₁(2) = 3, σ₂(2) = σ(3) = 4, σ₃(2) = σ(4) = 7, σ₄(2) = σ(7) = 8, ...
axiom sigma_chain_2 : sigmaIterate 1 2 = 3 ∧ sigmaIterate 2 2 = 4 ∧
    sigmaIterate 3 2 = 7 ∧ sigmaIterate 4 2 = 8

-- Growth rate for n = 2
-- 2^{1/0} undefined, 3^{1/1} = 3, 4^{1/2} = 2, 7^{1/3} ≈ 1.91, 8^{1/4} = √2 ≈ 1.68...
-- The conjecture says this should eventually exceed any bound

/-!
# Part 9: Connection to Multiplicativity

σ is multiplicative: σ(mn) = σ(m)σ(n) for gcd(m,n) = 1.
-/

-- σ is multiplicative
theorem sigma_multiplicative : ArithmeticFunction.IsMultiplicative (sigma 1) := by
  exact sigma_isMultiplicative

-- σ(p^k) = 1 + p + p² + ... + p^k = (p^{k+1} - 1)/(p - 1)
theorem sigma_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
    sigma 1 (p^k) = (p^(k+1) - 1) / (p - 1) := by
  sorry

/-!
# Part 10: Problem Status

The problem remains OPEN.
-/

-- The problem is open
def erdos_410_status : String := "OPEN"

-- Main formal statement
theorem erdos_410_statement : ErdosConjecture410 ↔
    ∀ n > 1, Tendsto (fun k : ℕ => ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  unfold ErdosConjecture410 growthRate sigmaIterate
  rfl

/-!
# Summary

**Problem:** Does lim_{k → ∞} σₖ(n)^{1/k} = ∞ for all n ≥ 2?

**Known:**
- σₖ(n) → ∞ as k → ∞ (the iterates grow without bound)
- σ is multiplicative with explicit formula for prime powers

**Unknown:**
- Whether the growth is "super-exponential" in the sense of the conjecture
- The answer for any specific n ≥ 2

**Related:** Aliquot sequences, perfect numbers, Guy Problem B9
-/

end Erdos410
