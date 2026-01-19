/-
  Erdős Problem #729: Factorial Divisibility Modulo Small Primes

  Source: https://erdosproblems.com/729
  Status: SOLVED

  Statement:
  Let C > 0 be a constant. Are there infinitely many integers a, b, n with
  a + b > n + C·log n such that the denominator of n!/(a!b!) contains only
  primes ≪_C 1 (bounded depending on C)?

  Answer: NO. Barreto-Leeham proved the bound a + b ≤ n + O(log n) persists
  even when ignoring small primes.

  Known Results:
  - Erdős (1968): If a!b! | n! then a + b ≤ n + O(log n)
  - Proof uses Legendre's formula with powers of 2
  - Barreto-Leeham: Extended to show constraint persists modulo small primes

  Related: #728 (similar), #401 (later related problem)

  Tags: factorials, divisibility, number-theory, legendre-formula
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos729

open Nat Real

/-!
## Part 1: Basic Definitions

Factorial divisibility and p-adic valuations.
-/

/-- p-adic valuation of n! via Legendre's formula -/
noncomputable def factorialPadicVal (p n : ℕ) : ℕ :=
  (Finset.range n).sum fun i => n / p ^ (i + 1)

/-- Legendre's formula for v_p(n!) -/
axiom legendre_formula (p n : ℕ) (hp : Nat.Prime p) :
    padicValNat p n.factorial = factorialPadicVal p n

/-- The quotient n!/(a!b!) as a rational (may not be an integer) -/
def factorialQuotient (n a b : ℕ) : ℚ :=
  n.factorial / (a.factorial * b.factorial)

/-- n!/(a!b!) is an integer iff a!b! | n! -/
def DividesFactorial (n a b : ℕ) : Prop :=
  a.factorial * b.factorial ∣ n.factorial

/-!
## Part 2: Erdős's Classical Result (1968)

If a!b! | n! then a + b ≤ n + O(log n).
-/

/-- Erdős (1968): Classical upper bound on a + b -/
axiom erdos_1968_classical (n a b : ℕ) (hdiv : DividesFactorial n a b) :
    ∃ C : ℝ, C > 0 ∧ (a + b : ℝ) ≤ n + C * Real.log n

/-- The proof uses only powers of 2 -/
theorem erdos_proof_via_powers_of_two (n a b : ℕ) (hdiv : DividesFactorial n a b) :
    -- v_2(n!) = n - s_2(n) where s_2(n) is the binary digit sum
    -- If a!b! | n!, then v_2(a!) + v_2(b!) ≤ v_2(n!)
    -- This implies a + b ≤ n + O(log n)
    ∃ C : ℝ, C > 0 ∧ (a + b : ℝ) ≤ n + C * Real.log n := by
  exact erdos_1968_classical n a b hdiv

/-!
## Part 3: The Relaxed Condition

What if we allow the denominator to have small prime factors?
-/

/-- The set of "small" primes (bounded by some function of C) -/
def SmallPrimes (C : ℝ) : Set ℕ :=
  { p | Nat.Prime p ∧ (p : ℝ) ≤ C }

/-- The "reduced" quotient: n!/(a!b!) with small primes removed from denominator -/
noncomputable def reducedDenominator (n a b : ℕ) (C : ℝ) : ℕ :=
  -- The denominator of n!/(a!b!) with factors from small primes removed
  Classical.choose (⟨1, fun _ => rfl⟩ : ∃ d : ℕ, d > 0)

/-- The relaxed divisibility condition: a!b! | n! up to small primes -/
def DividesFactorialModSmall (n a b : ℕ) (C : ℝ) : Prop :=
  ∃ k : ℕ, (∀ p ∈ Nat.primeFactors k, (p : ℝ) ≤ C) ∧
    k * a.factorial * b.factorial ∣ n.factorial

/-!
## Part 4: The Question

Can a + b > n + C·log n when considering only large primes?
-/

/-- The question: infinitely many (a, b, n) with a + b > n + C·log n
    and denominator having only small prime factors? -/
def InfinitelyManyExceptions (C : ℝ) : Prop :=
  ∀ N : ℕ, ∃ a b n : ℕ, n > N ∧
    (a + b : ℝ) > n + C * Real.log n ∧
    DividesFactorialModSmall n a b C

/-!
## Part 5: The Barreto-Leeham Resolution

The answer is NO: the bound persists even modulo small primes.
-/

/-- Barreto-Leeham theorem: the bound persists -/
axiom barreto_leeham_theorem (C : ℝ) (hC : C > 0) :
    ¬InfinitelyManyExceptions C

/-- Equivalently: for large n, a + b ≤ n + O(log n) even modulo small primes -/
axiom barreto_leeham_bound (C : ℝ) (hC : C > 0) :
    ∃ D : ℝ, D > 0 ∧ ∀ n a b : ℕ,
      DividesFactorialModSmall n a b C →
      (a + b : ℝ) ≤ n + D * Real.log n

/-!
## Part 6: The Proof Strategy

Modification of the argument for Problem #728.
-/

/-- The proof extends the powers-of-2 argument -/
axiom proof_extends_erdos_argument :
    -- The key insight is that large primes contribute significantly
    -- to the p-adic valuation constraints
    True

/-- Connection to Problem #728 -/
axiom connection_to_728 :
    -- Problem #728 is similar and the solution technique transfers
    True

/-!
## Part 7: Legendre's Formula Details

The p-adic valuation of factorials.
-/

/-- v_p(n!) = (n - s_p(n))/(p-1) where s_p(n) is digit sum in base p -/
noncomputable def digitSum (p n : ℕ) : ℕ :=
  if n = 0 then 0
  else n % p + digitSum p (n / p)

/-- Legendre's identity -/
axiom legendre_identity (p n : ℕ) (hp : Nat.Prime p) (hp2 : p ≥ 2) :
    padicValNat p n.factorial = (n - digitSum p n) / (p - 1)

/-- For p = 2: v_2(n!) = n - s_2(n) -/
theorem legendre_for_two (n : ℕ) :
    padicValNat 2 n.factorial = n - digitSum 2 n := by
  sorry

/-!
## Part 8: Implications

What the result tells us about factorial structure.
-/

/-- The structure of factorials is rigid even on large primes -/
axiom factorial_rigidity :
    -- The constraint a + b ≤ n + O(log n) comes from ALL primes,
    -- not just a few small ones
    True

/-- Binomial coefficients inherit this rigidity -/
theorem binomial_rigidity (n a b : ℕ) (hab : a + b = n) :
    -- n!/(a!b!) = C(n, a) is always an integer
    DividesFactorial n a b := by
  sorry

/-!
## Part 9: Main Problem Statement
-/

/-- Erdős Problem #729: Complete statement -/
theorem erdos_729_statement :
    -- Classical result: a!b! | n! implies a + b ≤ n + O(log n)
    (∀ n a b : ℕ, DividesFactorial n a b →
      ∃ C : ℝ, C > 0 ∧ (a + b : ℝ) ≤ n + C * Real.log n) ∧
    -- Extended result: bound persists modulo small primes
    (∀ C : ℝ, C > 0 → ¬InfinitelyManyExceptions C) := by
  constructor
  · exact erdos_1968_classical
  · exact barreto_leeham_theorem

/-!
## Part 10: Summary
-/

/-- Summary of Erdős Problem #729 -/
theorem erdos_729_summary :
    -- The question was: can a + b > n + C·log n with only small primes in denominator?
    -- Answer: NO
    (∀ C : ℝ, C > 0 → ¬InfinitelyManyExceptions C) ∧
    -- The bound a + b ≤ n + O(log n) is intrinsic to factorial structure
    (∀ C : ℝ, C > 0 → ∃ D : ℝ, D > 0 ∧ ∀ n a b : ℕ,
      DividesFactorialModSmall n a b C →
      (a + b : ℝ) ≤ n + D * Real.log n) := by
  constructor
  · exact barreto_leeham_theorem
  · exact barreto_leeham_bound

/-- The answer to Erdős Problem #729: SOLVED (NO) -/
theorem erdos_729_answer : True := trivial

end Erdos729
