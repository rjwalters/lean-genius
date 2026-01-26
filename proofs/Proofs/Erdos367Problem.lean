/-
Erdős Problem #367: Products of 2-Full Parts

**Problem Statement (OPEN)**

For a positive integer n, the 2-full part B₂(n) is n/n', where n' is the
product of primes dividing n exactly once (the squarefree part).
Equivalently, B₂(n) = ∏_{p² | n} p^{v_p(n)}.

For every fixed k ≥ 1, is it true that
  ∏_{n ≤ m < n+k} B₂(m) ≪ n^{2+o(1)} ?

Or perhaps even ≪_k n²?

**Known Results:**
- For k ≤ 2, the bound ≪ n² holds trivially (since B₂(n) ≤ n)
- For k ≥ 3, the strong bound ≪ n² fails (van Doorn)
- There exist infinitely many n with ∏_{n ≤ m < n+3} B₂(m) ≫ n²·log n

**Status**: OPEN

Reference: https://erdosproblems.com/367

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

open Nat Finset

namespace Erdos367

/-!
# Part 1: The 2-Full Part

The 2-full part B₂(n) captures prime powers p² and higher in
the factorization of n. It equals n divided by its squarefree part.
-/

/--
**Squarefree Part of n**

The product of primes dividing n exactly once (with exponent 1).
-/
noncomputable def squarefreePart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p = 1), p

/--
**The 2-Full Part B₂(n)**

B₂(n) = n / squarefreePart(n). This is the product of all prime
powers p^{v_p(n)} where v_p(n) ≥ 2.
-/
noncomputable def twoFullPart (n : ℕ) : ℕ :=
  if h : squarefreePart n ∣ n ∧ squarefreePart n ≠ 0
  then n / squarefreePart n
  else n

/--
**Alternative Definition via Prime Factorization**

B₂(n) = ∏_{v_p(n) ≥ 2} p^{v_p(n)}.
-/
noncomputable def twoFullPartAlt (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p ≥ 2),
    p ^ (n.factorization p)

/-!
# Part 2: Product over Consecutive Integers

The main object of study: the product of 2-full parts over k
consecutive integers starting at n.
-/

/--
**Product of 2-Full Parts over [n, n+k)**

∏_{n ≤ m < n+k} B₂(m)
-/
noncomputable def productTwoFullParts (n k : ℕ) : ℕ :=
  ∏ m ∈ Finset.Ico n (n + k), twoFullPart m

/-!
# Part 3: The Bounds

Two versions of the bound: weak (n^{2+ε}) and strong (n²).
-/

/--
**Weak Bound: n^{2+o(1)}**

For fixed k, ∏_{n ≤ m < n+k} B₂(m) ≤ C · n^{2+ε} for all ε > 0.
-/
def weakBound (k : ℕ) : Prop :=
  ∀ ε > 0, ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 1, (productTwoFullParts n k : ℝ) ≤ C * (n : ℝ) ^ (2 + ε)

/--
**Strong Bound: n²**

For fixed k, ∏_{n ≤ m < n+k} B₂(m) ≤ C_k · n².
-/
def strongBound (k : ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 1, (productTwoFullParts n k : ℝ) ≤ C * (n : ℝ) ^ 2

/-!
# Part 4: The Erdős Conjecture

The main open question: does the weak bound hold for all k?
-/

/--
**Erdős Problem #367 (OPEN)**

Does weakBound(k) hold for all k ≥ 1?

That is, for every fixed k, is ∏_{n ≤ m < n+k} B₂(m) ≪ n^{2+o(1)}?
-/
def erdos_367_conjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 → weakBound k

/-!
# Part 5: Known Results — Trivial Cases

For k ≤ 2, the strong bound holds because B₂(n) ≤ n.
-/

/--
**Trivial Case: k = 1**

B₂(n) ≤ n ≤ n², so strongBound(1) holds.
-/
axiom strong_bound_k1 : strongBound 1

/--
**Trivial Case: k = 2**

B₂(n) · B₂(n+1) ≤ n · (n+1) < 2n², so strongBound(2) holds.
-/
axiom strong_bound_k2 : strongBound 2

/-!
# Part 6: Known Results — Failure of Strong Bound

van Doorn showed the strong bound fails for k ≥ 3.
-/

/--
**Strong Bound Fails for k = 3**

There exist infinitely many n with ∏_{n ≤ m < n+3} B₂(m) ≫ n² · log n,
so no constant C can satisfy ∏B₂(m) ≤ C · n² for all n.
-/
axiom strong_bound_fails_k3 : ¬ strongBound 3

/--
**van Doorn's Lower Bound**

For k = 3, there exist infinitely many n where the product
of 2-full parts exceeds n² by a logarithmic factor.
-/
axiom van_doorn_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n ≥ N,
      (productTwoFullParts n 3 : ℝ) ≥ c * (n : ℝ) ^ 2 * Real.log n

/-!
# Part 7: Properties of the 2-Full Part

Basic properties of B₂(n) needed for the analysis.
-/

/--
**B₂(n) = 1 iff n is Squarefree**

The 2-full part is trivial exactly when n has no repeated prime factors.
-/
axiom twoFullPart_eq_one_iff (n : ℕ) (hn : n ≥ 1) :
    twoFullPart n = 1 ↔ Squarefree n

/--
**B₂(p) = 1 for Primes**

Primes are squarefree, so their 2-full part is 1.
-/
axiom twoFullPart_prime (p : ℕ) (hp : p.Prime) : twoFullPart p = 1

/--
**B₂(p²) = p² for Primes**

Perfect squares of primes are entirely 2-full.
-/
axiom twoFullPart_prime_sq (p : ℕ) (hp : p.Prime) : twoFullPart (p ^ 2) = p ^ 2

/--
**Multiplicativity on Coprime Arguments**

B₂(mn) = B₂(m) · B₂(n) when gcd(m,n) = 1.
-/
axiom twoFullPart_mul_coprime (m n : ℕ) (h : Nat.Coprime m n) :
    twoFullPart (m * n) = twoFullPart m * twoFullPart n

/--
**Upper Bound: B₂(n) ≤ n**

The 2-full part never exceeds n itself.
-/
axiom twoFullPart_le (n : ℕ) : twoFullPart n ≤ n

/--
**Divisibility: B₂(n) | n**

The 2-full part always divides n.
-/
axiom twoFullPart_dvd (n : ℕ) : twoFullPart n ∣ n

/-!
# Part 8: Generalization to r-Full Parts

The problem generalizes to r-full parts for r ≥ 3.
-/

/--
**r-Full Part of n**

B_r(n) = ∏_{v_p(n) ≥ r} p^{v_p(n)}: the product of prime powers
where the exponent is at least r.
-/
noncomputable def rFullPart (r n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p ≥ r),
    p ^ (n.factorization p)

/--
**Consistency: twoFullPartAlt = rFullPart 2**

The alternative 2-full definition is the r-full part with r = 2.
-/
theorem twoFullPart_eq_rFullPart (n : ℕ) : twoFullPartAlt n = rFullPart 2 n := rfl

/--
**Generalized Conjecture for r-Full Parts**

For r ≥ 3 and fixed k, does ∏_{n ≤ m < n+k} B_r(m) ≪ n^{r+o(1)}?
-/
def generalizedConjecture (r k : ℕ) : Prop :=
  ∀ ε > 0, ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 1, (∏ m ∈ Finset.Ico n (n + k), rFullPart r m : ℝ) ≤
      C * (n : ℝ) ^ (r + ε)

/-!
# Part 9: Heuristic Analysis

The average behavior of B₂(n) and why the problem is subtle.
-/

/--
**Average Behavior**

On average, B₂(n) is bounded (most numbers are nearly squarefree).
But the product over consecutive integers can be large because
nearby integers can share high prime powers.
-/
axiom average_twoFullPart_bounded :
    ∃ C : ℝ, C > 0 ∧ ∀ N ≥ 1,
      (∑ n ∈ Finset.Icc 1 N, (twoFullPart n : ℝ)) / N ≤ C

/-!
# Part 10: Summary
-/

/--
**Erdős Problem #367: Summary of Known Results**

Combines: strongBound holds for k ≤ 2, fails for k ≥ 3,
and the weak bound conjecture remains open.
-/
theorem erdos_367_summary :
    -- Strong bound holds for k = 1 and k = 2
    (strongBound 1 ∧ strongBound 2) ∧
    -- Strong bound fails for k = 3
    ¬ strongBound 3 ∧
    -- The weak bound conjecture is stated
    True :=
  ⟨⟨strong_bound_k1, strong_bound_k2⟩, strong_bound_fails_k3, trivial⟩

/-- The problem remains OPEN. -/
def erdos_367_status : String := "OPEN"

end Erdos367
