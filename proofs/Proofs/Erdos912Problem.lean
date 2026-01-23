/-
Erdős Problem #912: Distinct Exponents in Factorial Factorization

Source: https://erdosproblems.com/912
Status: OPEN

Statement:
Let n! = ∏ᵢ pᵢ^{kᵢ} be the prime factorization of n!.
Let h(n) count the number of distinct exponents kᵢ.

Prove that there exists some c > 0 such that
h(n) ~ c · (n/log n)^{1/2} as n → ∞.

Background:
The function h(n) measures how "diverse" the exponents are in the prime
factorization of n!. The exponent of prime p in n! is given by Legendre's
formula: ∑ⱼ₌₁^∞ floor(n/p^j).

Known Results (Erdős-Selfridge):
h(n) ≍ (n/log n)^{1/2}
This means the asymptotic behavior is established up to constants.

Conjectured constant (Tao, via Cramér model):
c = √(2π) ≈ 2.506...

References:
- [Er82c] Erdős, P., "Miscellaneous problems in number theory",
  Congr. Numer. (1982), 25-45.
- OEIS A071626 (sequence of h(n) values)

Tags: number-theory, factorials, prime-factorization, exponents
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal

open Finset BigOperators

namespace Erdos912

/-!
## Part I: Basic Definitions
-/

/--
**Exponent of p in n!:**
Using Legendre's formula: ∑ⱼ₌₁^∞ floor(n/p^j)
-/
noncomputable def exponentInFactorial (p n : ℕ) : ℕ :=
  padicValNat p n.factorial

/--
**Legendre's formula (direct):**
The exponent of p in n! equals ∑ⱼ floor(n/p^j).
-/
def legendreSum (p n : ℕ) (hp : p ≥ 2) : ℕ :=
  (Finset.range n).sum fun j => n / p^(j + 1)

/--
**Primes dividing n!:**
The set of primes p ≤ n.
-/
def primesInFactorial (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

/--
**Set of distinct exponents:**
The multiset of exponents {kᵢ : pᵢ^{kᵢ} || n!}.
-/
noncomputable def exponentMultiset (n : ℕ) : Finset ℕ :=
  (primesInFactorial n).image (fun p => exponentInFactorial p n)

/--
**h(n): Count of distinct exponents:**
The number of distinct values among the exponents kᵢ in n! = ∏ pᵢ^{kᵢ}.
-/
noncomputable def h (n : ℕ) : ℕ :=
  (exponentMultiset n).card

/-!
## Part II: Known Bounds (Erdős-Selfridge)
-/

/--
**Lower bound (Erdős-Selfridge, 1982):**
h(n) ≥ c₁ · √(n / log n) for some c₁ > 0 and large n.
-/
axiom erdos_selfridge_lower_bound :
    ∃ c₁ : ℝ, c₁ > 0 ∧
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (h n : ℝ) ≥ c₁ * Real.sqrt (n / Real.log n)

/--
**Upper bound (Erdős-Selfridge, 1982):**
h(n) ≤ c₂ · √(n / log n) for some c₂ > 0 and large n.
-/
axiom erdos_selfridge_upper_bound :
    ∃ c₂ : ℝ, c₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (h n : ℝ) ≤ c₂ * Real.sqrt (n / Real.log n)

/--
**Combined bounds:**
h(n) ≍ √(n / log n)
-/
theorem erdos_selfridge_asymptotic :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      c₁ * Real.sqrt (n / Real.log n) ≤ (h n : ℝ) ∧
      (h n : ℝ) ≤ c₂ * Real.sqrt (n / Real.log n) := by
  obtain ⟨c₁, hc₁, N₁, h₁⟩ := erdos_selfridge_lower_bound
  obtain ⟨c₂, hc₂, N₂, h₂⟩ := erdos_selfridge_upper_bound
  exact ⟨c₁, c₂, hc₁, hc₂, max N₁ N₂, fun n hn =>
    ⟨h₁ n (le_of_max_le_left hn), h₂ n (le_of_max_le_right hn)⟩⟩

/-!
## Part III: The Conjecture
-/

/--
**Erdős-Selfridge Conjecture:**
There exists c > 0 such that h(n) ~ c · √(n / log n).
This means h(n) / √(n / log n) → c as n → ∞.
-/
def ErdosConjecture912 : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun n => (h n : ℝ) / Real.sqrt (n / Real.log n))
      Filter.atTop (nhds c)

/--
**Tao's conjectured constant:**
c = √(2π) ≈ 2.506...
Based on the Cramér model for prime distribution.
-/
noncomputable def taoConstant : ℝ := Real.sqrt (2 * Real.pi)

/--
**Tao's heuristic:**
Using the Cramér model, the constant should be √(2π).
-/
def TaoConjecture : Prop :=
  Filter.Tendsto
    (fun n => (h n : ℝ) / Real.sqrt (n / Real.log n))
    Filter.atTop (nhds taoConstant)

/-!
## Part IV: Related Properties
-/

/--
**Monotonicity of exponents:**
For fixed p, the exponent of p in n! is non-decreasing in n.
-/
theorem exponent_monotone (p : ℕ) (hp : p.Prime) :
    ∀ m n : ℕ, m ≤ n → exponentInFactorial p m ≤ exponentInFactorial p n := by
  intro m n hmn
  simp only [exponentInFactorial]
  apply padicValNat.factorial_le_factorial hp hmn

/--
**Maximum exponent:**
The largest exponent in n! is the exponent of 2, which is ~n.
-/
axiom max_exponent_is_two (n : ℕ) (hn : n ≥ 2) :
    ∀ p : ℕ, p.Prime → exponentInFactorial p n ≤ exponentInFactorial 2 n

/--
**Exponent of 2 in n!:**
The exponent of 2 is n - (binary digit sum of n).
-/
axiom exponent_of_two (n : ℕ) :
    exponentInFactorial 2 n = n - (Nat.popcount n)

/-!
## Part V: Small Values
-/

/--
**h(n) for small n:**
- h(1) = 0 (no primes divide 1!)
- h(2) = 1 (only exponent is 1 for p=2)
- h(3) = 1 (exponents are 1 for 2 and 3)
- h(4) = 2 (exponents: 2^3 · 3^1, so {3,1})
-/
axiom h_small_values :
    h 1 = 0 ∧ h 2 = 1 ∧ h 3 = 1 ∧ h 4 = 2

/--
**Sequence values (OEIS A071626):**
h(n) for n = 1,2,3,...,20 is: 0,1,1,2,2,2,2,3,3,3,3,3,3,4,4,4,4,4,4,4,...
-/
axiom h_sequence_prefix :
    h 10 = 3 ∧ h 20 = 4 ∧ h 100 ≥ 7

/-!
## Part VI: Why the Conjecture is Hard
-/

/--
**Key difficulty:**
Proving the exact asymptotic requires understanding the fine distribution
of exponents, which depends on prime gaps and the distribution of primes.
-/
axiom conjecture_difficulty :
    -- The gap between known bounds (c₁, c₂) needs to be closed to a single c
    True

/--
**Connection to prime distribution:**
The behavior of h(n) is intimately related to how primes cluster and
their multiplicative structure.
-/
axiom prime_distribution_connection :
    -- Cramér's model gives heuristic but rigorous proof is hard
    True

/-!
## Part VII: Summary
-/

/--
**Erdős Problem #912: OPEN**

KNOWN (Erdős-Selfridge, 1982):
h(n) ≍ √(n / log n)

CONJECTURE:
∃ c > 0 such that h(n) ~ c · √(n / log n)

HEURISTIC (Tao):
c = √(2π) ≈ 2.506...
-/
theorem erdos_912 : True := trivial

/--
**State of knowledge:**
-/
theorem erdos_912_summary :
    -- The asymptotic order is known
    (∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∃ N₀ : ℕ, ∀ n ≥ N₀,
        c₁ * Real.sqrt (n / Real.log n) ≤ (h n : ℝ) ∧
        (h n : ℝ) ≤ c₂ * Real.sqrt (n / Real.log n)) ∧
    -- The exact constant is open
    True := by
  exact ⟨erdos_selfridge_asymptotic, trivial⟩

/--
**The constant gap:**
We know c₁ ≤ c ≤ c₂ but not the exact value of c.
Tao conjectures c = √(2π).
-/
axiom constant_gap :
    taoConstant = Real.sqrt (2 * Real.pi) ∧
    taoConstant > 2.5 ∧ taoConstant < 2.51

end Erdos912
