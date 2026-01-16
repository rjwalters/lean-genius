/-
Erdős Problem #248: Bounded ω(n+k) for Consecutive Integers

Are there infinitely many n such that ω(n+k) ≪ k for all k ≥ 1?
Here ω(n) is the number of distinct prime divisors of n.

**Answer**: YES — proved by Tao and Teräväinen (2025)

They showed there exists an absolute constant C > 0 such that for infinitely
many n, for all k ≥ 1: ω(n+k) ≤ C·k.

This is a remarkable result connecting:
- The prime omega function ω(n) (distinct prime divisors)
- The behavior of arithmetic functions along arithmetic progressions
- Sieve methods in analytic number theory

References:
- Original: Erdős and Graham (1980), "Old and new problems in combinatorial
  number theory"
- Solution: Tao and Teräväinen (2025), "Quantitative correlations and some
  problems on prime factors of consecutive integers", arXiv:2512.01739

Source: https://erdosproblems.com/248
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

/-!
## Prime Omega Function

The function ω(n) counts the number of distinct prime divisors of n.
For example:
- ω(1) = 0 (no prime divisors)
- ω(2) = 1 (only prime 2)
- ω(6) = 2 (primes 2 and 3)
- ω(30) = 3 (primes 2, 3, and 5)

In Mathlib, ω(n) = n.primeFactors.card
-/

/-- The prime omega function ω(n): number of distinct prime divisors of n.
    Defined using Mathlib's primeFactors which gives the set of prime divisors. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- ω(1) = 0: the number 1 has no prime divisors. -/
theorem omega_one : omega 1 = 0 := by native_decide

/-- ω(2) = 1: the only prime divisor of 2 is itself. -/
theorem omega_two : omega 2 = 1 := by native_decide

/-- ω(6) = 2: prime divisors are 2 and 3. -/
theorem omega_six : omega 6 = 2 := by native_decide

/-- ω(30) = 3: prime divisors are 2, 3, and 5. -/
theorem omega_thirty : omega 30 = 3 := by native_decide

/-!
## The Erdős Problem

Erdős asked whether there are infinitely many "smooth-tail" integers n
such that as we look at n+1, n+2, n+3, ..., the number of distinct prime
divisors grows at most linearly: ω(n+k) ≤ C·k for some absolute constant C.

This is surprising because typically ω(n) ≈ log log n for "generic" n,
so most integers don't have this property.
-/

/-- The set of integers n satisfying Erdős's condition:
    ω(n+k) ≤ C·k for all k ≥ 1. -/
def smoothTailIntegers (C : ℝ) : Set ℕ :=
  {n : ℕ | ∀ k : ℕ, k ≥ 1 → (omega (n + k) : ℝ) ≤ C * (k : ℝ)}

/-- Erdős Problem #248 statement: there exists C > 0 such that
    infinitely many n satisfy ω(n+k) ≤ C·k for all k ≥ 1.

This was proved by Tao and Teräväinen in 2025 using sophisticated
sieve methods and correlation estimates for arithmetic functions.

The key insight is that while ω(n) typically grows like log log n,
there exist infinitely many "exceptional" starting points n where
the subsequent values n+1, n+2, ... have unusually few prime factors.

We state this as an axiom because:
1. The proof requires deep results about correlations of multiplicative functions
2. The sieve theory methods used are not yet formalized in Mathlib
3. The result was only recently proved (December 2025)
-/
axiom erdos_248 : ∃ C : ℝ, C > 0 ∧ (smoothTailIntegers C).Infinite

/-!
## Verified Examples

We can verify small examples using native_decide.
-/

/-- ω(p) = 1 for any prime p, since the only prime divisor of p is itself. -/
theorem omega_prime {p : ℕ} (hp : p.Prime) : omega p = 1 := by
  unfold omega
  rw [hp.primeFactors]
  simp

/-- The smooth-tail condition holds at n=1 for small k with C=2.
    For example, ω(2) = 1 ≤ 2, ω(3) = 1 ≤ 4, etc. -/
theorem smooth_tail_n1_k1 : (omega (1 + 1) : ℕ) ≤ 2 * 1 := by native_decide

theorem smooth_tail_n1_k2 : (omega (1 + 2) : ℕ) ≤ 2 * 2 := by native_decide

theorem smooth_tail_n1_k3 : (omega (1 + 3) : ℕ) ≤ 2 * 3 := by native_decide

theorem smooth_tail_n1_k4 : (omega (1 + 4) : ℕ) ≤ 2 * 4 := by native_decide

theorem smooth_tail_n1_k5 : (omega (1 + 5) : ℕ) ≤ 2 * 5 := by native_decide

/-!
## Historical Context

Erdős and Graham wrote about this problem in 1980: "we just know too little
about sieves to be able to handle such a question" - referring to the
collective knowledge of the mathematical community at the time.

The resolution by Tao and Teräväinen 45 years later shows how far sieve
theory and our understanding of correlations between arithmetic functions
has advanced. Their 2025 paper establishes quantitative bounds on the
distribution of prime factors of consecutive integers.
-/

/-- The set of smooth-tail integers is nonempty (witnessed by the axiom). -/
theorem smoothTailIntegers_nonempty : ∃ C : ℝ, C > 0 ∧ (smoothTailIntegers C).Nonempty := by
  obtain ⟨C, hC_pos, hC_inf⟩ := erdos_248
  exact ⟨C, hC_pos, Set.Infinite.nonempty hC_inf⟩
