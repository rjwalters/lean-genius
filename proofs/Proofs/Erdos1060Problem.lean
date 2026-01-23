/-
Erdős Problem #1060: Counting Solutions to k·σ(k) = n

Source: https://erdosproblems.com/1060
Status: OPEN (Problem B11 in Guy's collection)

Statement:
Let f(n) count the number of solutions to k·σ(k) = n, where σ(k) is the
sum of divisors of k.

Questions:
1. Is f(n) ≤ n^{o(1/log log n)}?
2. Perhaps even f(n) ≤ (log n)^{O(1)}?

Note: σ(k) is the sum of all divisors of k. For example:
- σ(1) = 1, so 1·σ(1) = 1
- σ(6) = 1+2+3+6 = 12, so 6·σ(6) = 72
- σ(p) = p+1 for prime p, so p·σ(p) = p(p+1)

Tags: Number theory, Divisor functions, Counting solutions
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Finset

namespace Erdos1060

/-
## Part I: The Sum of Divisors Function
-/

/--
Sum of divisors function σ(k) = sum of all divisors of k.
-/
abbrev sigma (k : ℕ) : ℕ := (Nat.divisors k).sum id

/--
σ(1) = 1
-/
theorem sigma_one : sigma 1 = 1 := by
  simp [sigma, Nat.divisors]

/--
For prime p, σ(p) = p + 1
-/
theorem sigma_prime (p : ℕ) (hp : p.Prime) : sigma p = p + 1 := by
  simp [sigma, Nat.Prime.divisors hp]
  ring

/--
σ is multiplicative on coprime arguments.
-/
theorem sigma_mul_coprime (m n : ℕ) (hmn : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
    sigma (m * n) = sigma m * sigma n := by
  sorry

/-
## Part II: The Product k·σ(k)
-/

/--
The product function g(k) = k · σ(k).
-/
def g (k : ℕ) : ℕ := k * sigma k

/--
g(1) = 1
-/
theorem g_one : g 1 = 1 := by
  simp [g, sigma_one]

/--
For prime p, g(p) = p(p+1).
-/
theorem g_prime (p : ℕ) (hp : p.Prime) : g p = p * (p + 1) := by
  simp [g, sigma_prime p hp]

/-
## Part III: The Counting Function f(n)
-/

/--
The set of k such that k·σ(k) = n.
-/
def solutionSet (n : ℕ) : Set ℕ := {k : ℕ | g k = n}

/--
f(n) = number of solutions to k·σ(k) = n.

Note: We need to show this is finite for n > 0 to define f(n) properly.
-/
noncomputable def f (n : ℕ) : ℕ := (solutionSet n).ncard

/--
The solution set is finite for any n > 0.
Proof: k·σ(k) ≥ k·1 = k (since 1 | k for k > 0), so k ≤ n.
-/
theorem solutionSet_finite (n : ℕ) (hn : n > 0) : (solutionSet n).Finite := by
  refine Set.Finite.subset (Set.finite_Icc 1 n) ?_
  intro k hk
  simp only [solutionSet, Set.mem_setOf_eq] at hk
  simp only [Set.mem_Icc]
  constructor
  · -- k ≥ 1: if k = 0, then g(k) = 0 ≠ n (since n > 0)
    by_contra h
    push_neg at h
    interval_cases k
    simp [g, sigma] at hk
    omega
  · -- k ≤ n: since k·σ(k) ≥ k (as σ(k) ≥ 1 for k > 0)
    sorry

/--
Alternative definition using Finset for finite n.
-/
noncomputable def f' (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => g k = n)).card

/--
f and f' agree for n > 0.
-/
theorem f_eq_f' (n : ℕ) (hn : n > 0) : f n = f' n := by
  sorry

/-
## Part IV: Basic Values
-/

/--
f(1) = 1: The only solution to k·σ(k) = 1 is k = 1.
-/
theorem f_of_one : f 1 = 1 := by
  sorry

/--
f(0) = 0: There are no solutions to k·σ(k) = 0 for k > 0.
(For k = 0, g(0) = 0, but we typically exclude k = 0.)
-/
theorem f_of_zero : f 0 = 0 := by
  sorry

/-
## Part V: Upper Bound Conjectures (OPEN)
-/

/--
**Weak Conjecture:**
f(n) ≤ n^{o(1/log log n)} as n → ∞.

This means: For any ε > 0, there exists N such that for all n > N,
f(n) ≤ n^{ε/log log n}.
-/
axiom erdos_1060_weak_conjecture :
    ∀ ε > 0, ∃ N : ℕ, ∀ n > N,
      (f n : ℝ) ≤ (n : ℝ) ^ (ε / Real.log (Real.log n))

/--
**Strong Conjecture:**
f(n) ≤ (log n)^C for some constant C.

This is a much stronger bound - polynomial in log n rather than
a slow power of n.
-/
axiom erdos_1060_strong_conjecture :
    ∃ C : ℝ, ∀ n > 1,
      (f n : ℝ) ≤ (Real.log n) ^ C

/-
## Part VI: OEIS Connection
-/

/--
OEIS A327153 contains values related to this problem.
The sequence of n for which f(n) > 0 (i.e., k·σ(k) = n has a solution).
-/
def oeis_A327153 : Set ℕ := {n : ℕ | f n > 0}

/--
Membership in A327153.
-/
theorem mem_A327153_iff (n : ℕ) :
    n ∈ oeis_A327153 ↔ ∃ k > 0, g k = n := by
  simp [oeis_A327153, f, solutionSet, Set.ncard_pos]
  constructor
  · intro ⟨hne, _⟩
    obtain ⟨k, hk⟩ := Set.nonempty_of_ncard_ne_zero (fun h => hne h)
    use k
    sorry -- Need to show k > 0 from k ∈ solutionSet n
  · intro ⟨k, hk_pos, hgk⟩
    constructor
    · intro h
      have : k ∈ solutionSet n := hgk
      rw [h] at this
      simp at this
    · exact ⟨k, hgk⟩

/-
## Part VII: Examples and Computations
-/

/--
n = 1: k = 1 is the only solution (1·σ(1) = 1·1 = 1).
-/
example : g 1 = 1 := g_one

/--
n = 6: k = 2 gives 2·σ(2) = 2·3 = 6.
-/
example : g 2 = 6 := by
  simp [g, sigma]
  native_decide

/--
n = 12: k = 3 gives 3·σ(3) = 3·4 = 12.
-/
example : g 3 = 12 := by
  simp [g, sigma]
  native_decide

/--
n = 72: k = 6 gives 6·σ(6) = 6·12 = 72.
-/
example : g 6 = 72 := by
  simp [g, sigma]
  native_decide

/--
For prime p: g(p) = p(p+1).
Examples:
- g(2) = 6, g(3) = 12, g(5) = 30, g(7) = 56
-/
example : g 5 = 30 := by simp [g, sigma]; native_decide
example : g 7 = 56 := by simp [g, sigma]; native_decide

end Erdos1060
