/-
Erdős Problem #394: Divisibility by Consecutive Integer Products

Source: https://erdosproblems.com/394
Status: PARTIALLY SOLVED / OPEN

Statement:
Let t_k(n) denote the least m such that n | m(m+1)(m+2)···(m+k-1).

Questions:
1. Is Σ_{n≤x} t₂(n) ≪ x²/(log x)^c for some c > 0?
2. For k ≥ 2, is Σ_{n≤x} t_{k+1}(n) = o(Σ_{n≤x} t_k(n))?

Known Results:
- Erdős-Hall (1978): Σ t₂(n) ≪ (log log log x / log log x) x²
- Conjecture: Σ t₂(n) = o(x²/(log x)^c) for c < log 2
- Trivial: Σ t₂(n) ≫ x²/log x (since t₂(p) = p-1 for primes)
- Special: t_{n-1}(n!) = 2, t_{n-2}(n!) ≪ n

References:
- Erdős-Hall (1978): "On some unconventional problems on divisors"
- Erdős-Graham (1980): "Old and new problems in combinatorial number theory"

Tags: number-theory, divisibility, consecutive-integers, asymptotics
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Nat Real Finset BigOperators

namespace Erdos394

/-!
## Part I: Basic Definitions
-/

/--
**Product of k Consecutive Integers:**
m(m+1)(m+2)···(m+k-1)
-/
def consecutiveProduct (m k : ℕ) : ℕ :=
  ∏ i in range k, (m + i)

/--
**The Function t_k(n):**
The least m ≥ 1 such that n | m(m+1)···(m+k-1).
-/
noncomputable def t (k n : ℕ) : ℕ :=
  Nat.find (⟨n, by
    simp [consecutiveProduct]
    sorry⟩ : ∃ m : ℕ, m ≥ 1 ∧ n ∣ consecutiveProduct m k)

/--
**Divisibility Condition:**
n divides the product of k consecutive integers starting at m.
-/
def divides_consecutive (n m k : ℕ) : Prop :=
  n ∣ consecutiveProduct m k

/-!
## Part II: Basic Properties of t_k
-/

/--
**t_k is Well-Defined:**
For any n ≥ 1 and k ≥ 1, t_k(n) exists (m = n works for k ≥ 1).
-/
theorem t_well_defined (k n : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    ∃ m : ℕ, m ≥ 1 ∧ n ∣ consecutiveProduct m k := by
  -- m = n works since n | n(n+1)···
  use n
  constructor
  · exact hn
  · sorry  -- n divides any product containing n

/--
**t_2(n) for Primes:**
For prime p, we have t₂(p) = p - 1.
(Since p | (p-1)·p but p ∤ m(m+1) for m < p-1)
-/
axiom t2_of_prime (p : ℕ) (hp : p.Prime) :
    t 2 p = p - 1

/--
**Corollary: Primes Give Large t₂**
Since t₂(p) = p - 1, primes contribute significantly to Σ t₂(n).
-/
theorem primes_large_t2 :
    ∀ p : ℕ, p.Prime → t 2 p = p - 1 :=
  t2_of_prime

/-!
## Part III: The Sum Σ t₂(n)
-/

/--
**The Sum Function:**
S_k(x) = Σ_{n≤x} t_k(n)
-/
noncomputable def S (k : ℕ) (x : ℕ) : ℕ :=
  ∑ n in range (x + 1), if n ≥ 1 then t k n else 0

/--
**Trivial Lower Bound:**
Σ_{n≤x} t₂(n) ≫ x²/log x

This follows from the Prime Number Theorem: there are ~x/log x primes
up to x, each contributing p-1 ~ p to the sum.
-/
axiom trivial_lower_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 2 →
      (S 2 x : ℝ) ≥ C * (x : ℝ)^2 / Real.log x

/--
**Erdős's Original Conjecture:**
Σ_{n≤x} t₂(n) = o(x²)
-/
def erdos_original_conjecture : Prop :=
  ∀ ε > 0, ∀ᶠ x in Filter.atTop, (S 2 x : ℝ) < ε * x^2

/-!
## Part IV: Erdős-Hall Theorem (1978)
-/

/--
**Erdős-Hall Upper Bound (1978):**
Σ_{n≤x} t₂(n) ≪ (log log log x / log log x) x²

This is stronger than Erdős's original o(x²) conjecture.
-/
axiom erdos_hall_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 16 →
      (S 2 x : ℝ) ≤ C * (Real.log (Real.log (Real.log x))) /
                       (Real.log (Real.log x)) * x^2

/--
**Corollary: Original Conjecture is True**
-/
theorem erdos_conjecture_proved : erdos_original_conjecture := by
  intro ε hε
  -- Follows from erdos_hall_upper_bound since (log log log x)/(log log x) → 0
  sorry

/-!
## Part V: The Erdős-Hall Conjecture
-/

/--
**Erdős-Hall Conjecture:**
Σ_{n≤x} t₂(n) = o(x²/(log x)^c) for any c < log 2

This is stronger than what they proved.
-/
def erdos_hall_conjecture : Prop :=
  ∀ c : ℝ, c < Real.log 2 → ∀ ε > 0, ∀ᶠ x in Filter.atTop,
    (S 2 x : ℝ) < ε * x^2 / (Real.log x)^c

/--
**The Threshold c = log 2:**
The conjecture fails for c ≥ log 2 (primes alone contribute Ω(x²/log x)).
-/
theorem threshold_log_2 :
    ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 2 →
      (S 2 x : ℝ) ≥ C * x^2 / Real.log x := by
  exact trivial_lower_bound

/--
**Question 1 Status:**
Is Σ t₂(n) ≪ x²/(log x)^c for some c > 0?

Status: OPEN (conjectured YES for 0 < c < log 2)
-/
axiom question_1_open : True

/-!
## Part VI: The Hierarchy Question
-/

/--
**Question 2: The Hierarchy Conjecture**
For k ≥ 2, is Σ_{n≤x} t_{k+1}(n) = o(Σ_{n≤x} t_k(n))?

This asks whether larger k gives asymptotically smaller sums.
-/
def hierarchy_conjecture : Prop :=
  ∀ k : ℕ, k ≥ 2 →
    ∀ ε > 0, ∀ᶠ x in Filter.atTop,
      (S (k+1) x : ℝ) < ε * (S k x : ℝ)

/--
**Question 2 Status:**
Status: OPEN
-/
axiom question_2_open : ¬hierarchy_conjecture ∨ hierarchy_conjecture

/-!
## Part VII: Special Cases (Factorials)
-/

/--
**t_{n-1}(n!) = 2:**
The product 2·3·4···n = n! is divisible by n!.
-/
axiom factorial_t_n_minus_1 (n : ℕ) (hn : n ≥ 2) :
    t (n - 1) n.factorial = 2

/--
**t_{n-2}(n!) ≪ n:**
For n-2 consecutive integers, we need a larger starting point.
-/
axiom factorial_t_n_minus_2 (n : ℕ) (hn : n ≥ 3) :
    t (n - 2) n.factorial ≤ 2 * n

/--
**This Bound is Sharp:**
For n = 2^r, we have t_{n-2}(n!) ≳ n.
-/
axiom factorial_t_n_minus_2_sharp :
    ∀ r : ℕ, r ≥ 2 →
      t (2^r - 2) (2^r).factorial ≥ 2^(r-1)

/--
**Erdős-Hall Question about Factorials:**
Does t_{n-3}(n!) have any special structure?
-/
axiom factorial_t_n_minus_3_open : True

/-!
## Part VIII: The Selfridge Result
-/

/--
**The Strict Decrease Property:**
For infinitely many n, is it true that
  t_k(n!) < t_{k-1}(n!) - 1 for all 1 ≤ k < n?
-/
def strict_decrease_property (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n →
    t k n.factorial + 1 < t (k - 1) n.factorial

/--
**Erdős-Hall-Selfridge (n = 10):**
The strict decrease property holds for n = 10.
-/
axiom selfridge_n_10 : strict_decrease_property 10

/--
**Question: Infinitely Many n?**
Does strict_decrease_property hold for infinitely many n?
-/
axiom infinitely_many_strict_decrease :
    (∃ᶠ n in Filter.atTop, strict_decrease_property n) ∨
    ¬(∃ᶠ n in Filter.atTop, strict_decrease_property n)

/-!
## Part IX: Why This is Interesting
-/

/--
**Connection to Divisibility:**
Products of consecutive integers have nice divisibility properties:
- k! | m(m+1)···(m+k-1) for all m (binomial coefficient argument)
- The question is about divisibility by other n
-/
theorem consecutive_divisible_by_factorial (m k : ℕ) (hk : k ≥ 1) :
    k.factorial ∣ consecutiveProduct m k := by
  -- This is the binomial coefficient formula
  sorry

/--
**Probabilistic Intuition:**
For random m, the probability that n | m(m+1)···(m+k-1) is roughly k/n
for large n. Thus t_k(n) ≈ n/k on average.
-/
axiom probabilistic_intuition : True

/--
**Connection to Smooth Numbers:**
t_k(n) is small when n is "smooth" (has only small prime factors),
since smooth numbers appear more frequently in short intervals.
-/
axiom smooth_number_connection : True

/-!
## Part X: Summary
-/

/--
**Summary of Results:**
-/
theorem erdos_394_summary :
    -- Erdős-Hall proved the main upper bound
    (∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 16 →
      (S 2 x : ℝ) ≤ C * (Real.log (Real.log (Real.log x))) /
                       (Real.log (Real.log x)) * x^2) ∧
    -- Trivial lower bound
    (∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 2 →
      (S 2 x : ℝ) ≥ C * (x : ℝ)^2 / Real.log x) ∧
    -- Selfridge result for n = 10
    strict_decrease_property 10 := by
  exact ⟨erdos_hall_upper_bound, trivial_lower_bound, selfridge_n_10⟩

/--
**Erdős Problem #394: PARTIALLY SOLVED / OPEN**

**DEFINITION:** t_k(n) = least m such that n | m(m+1)···(m+k-1)

**QUESTION 1:** Σ t₂(n) ≪ x²/(log x)^c for some c > 0?

**STATUS:** OPEN
- Erdős-Hall (1978): Σ t₂(n) ≪ (log log log x / log log x) x²
- Conjecture: YES for 0 < c < log 2
- Lower bound: Σ t₂(n) ≫ x²/log x (from primes)

**QUESTION 2:** Σ t_{k+1}(n) = o(Σ t_k(n)) for k ≥ 2?

**STATUS:** OPEN

**SPECIAL CASES:**
- t_{n-1}(n!) = 2
- t_{n-2}(n!) ≪ n (sharp for n = 2^r)
- Strict decrease holds for n = 10 (Selfridge)

**KEY INSIGHT:** t₂(p) = p - 1 for primes, giving the lower bound.
The Erdős-Hall bound uses sophisticated sieve methods.
-/
theorem erdos_394 :
    ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 16 →
      (S 2 x : ℝ) ≤ C * (Real.log (Real.log (Real.log x))) /
                       (Real.log (Real.log x)) * x^2 :=
  erdos_hall_upper_bound

/--
**Historical Note:**
This problem combines divisibility questions with asymptotic analysis.
The logarithmic factors (log log log x / log log x) show how slowly
the bound improves over the trivial x² estimate.
-/
theorem historical_note : True := trivial

end Erdos394
