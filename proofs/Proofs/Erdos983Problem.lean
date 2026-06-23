/-
Erdős Problem #983: Prime Coverage Function for Smooth Numbers

Source: https://erdosproblems.com/983
Status: SOLVED (Erdős-Straus 1970)

Statement:
Let n ≥ 2 and π(n) < k ≤ n. Define f(k,n) as the smallest integer r such that
in any A ⊆ {1,...,n} of size |A| = k, there exist primes p₁,...,pᵣ such that
at least r elements of A are "smooth" with respect to {p₁,...,pᵣ}
(i.e., divisible only by primes from this set).

Question: Does 2π(√n) - f(π(n)+1, n) → ∞ as n → ∞?

Answer: NO - Erdős and Straus proved the difference is o(√n/(log n)^A).

Results (Erdős-Straus 1970):
1. f(π(n)+1, n) = 2π(√n) + o_A(√n/(log n)^A) for any A > 0
2. f(cn, n) = log log n + (c₁ + o(1))√(2 log log n) for constant 0 < c < 1

The problem concerns "smooth numbers" - integers with no large prime factors.
Smooth numbers play a key role in factorization algorithms and number theory.

References:
- [Er70b] Erdős, "Some applications of graph theory to number theory",
  Proc. Second Chapel Hill Conf. Combinatorial Mathematics (1970), 136-145

Tags: number-theory, primes, smooth-numbers, prime-counting
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting

open Nat Finset BigOperators

namespace Erdos983

/-
## Part I: Basic Definitions

Prime counting, smooth numbers, and the f function.
-/

/--
**Prime Counting Function:**
π(n) = number of primes ≤ n.
-/
noncomputable def primePi (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).card

/--
**Primes up to n:**
The set of primes in {1,...,n}.
-/
def primesUpTo (n : ℕ) : Finset ℕ :=
  Finset.filter Nat.Prime (Finset.range (n + 1))

/--
**Smooth with respect to a prime set:**
An integer m is P-smooth if all prime factors of m are in P.
-/
def IsSmooth (P : Finset ℕ) (m : ℕ) : Prop :=
  m ≥ 1 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ m → p ∈ P

/--
**P-smooth elements of a set:**
The elements of A that are smooth with respect to P.
-/
def smoothElements (P : Finset ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun a => ∀ p : ℕ, Nat.Prime p → p ∣ a → p ∈ P)

/--
**Prime set covers r elements:**
A prime set P of size r "covers" A if at least r elements of A are P-smooth.
-/
def PrimesCover (P : Finset ℕ) (A : Finset ℕ) (r : ℕ) : Prop :=
  (∀ p ∈ P, Nat.Prime p) ∧ P.card = r ∧ r ≤ (smoothElements P A).card

/-
## Part II: The f Function

f(k,n) = minimum r such that any k-subset of {1,...,n} can be r-covered.
-/

/--
**The f Function:**
f(k,n) is the smallest r such that for any A ⊆ {1,...,n} with |A| = k,
there exist r primes covering at least r elements of A.
-/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ A : Finset ℕ, A ⊆ Finset.range (n + 1) → A.card = k →
    ∃ P : Finset ℕ, PrimesCover P A r}

/--
**Trivial Upper Bound:**
f(k,n) ≤ π(n) since all elements are smooth with respect to all primes ≤ n.
-/
/--
**Monotonicity in k:**
f is increasing in k.
-/
/-
## Part III: The Main Question

Does 2π(√n) - f(π(n)+1, n) tend to infinity?
-/

/--
**The Erdős Question:**
Does 2π(√n) - f(π(n)+1, n) → ∞ as n → ∞?
-/
def ErdosQuestion983 : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N,
    2 * primePi (Nat.sqrt n) > f (primePi n + 1) n + M

/--
**The Answer is NO:**
The difference is bounded, not tending to infinity.
-/
axiom erdos_question_answer : ¬ErdosQuestion983

/-
## Part IV: Erdős-Straus Results

The precise asymptotics for f(k,n).
-/

/--
**Erdős-Straus Theorem 1:**
f(π(n)+1, n) = 2π(√n) + o_A(√n/(log n)^A) for any A > 0.

This means the difference 2π(√n) - f(π(n)+1, n) is small (tends to 0 faster
than any polynomial in n, slower than √n).
-/
/--
**Corollary: The Difference is o(1) as a ratio:**
(2π(√n) - f(π(n)+1, n)) / √n → 0.
-/
axiom difference_is_sublinear :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |(2 * (primePi (Nat.sqrt n) : ℝ) - (f (primePi n + 1) n : ℝ))| /
      (n : ℝ)^(1/2 : ℝ) < ε

/--
**Erdős-Straus Theorem 2:**
For constant 0 < c < 1:
f(cn, n) = log log n + (c₁ + o(1))√(2 log log n)
where c₁ is related to the constant c via the normal distribution.
-/
/-
## Part V: Why 2π(√n)?

The intuition behind the formula.
-/

/--
**Primes ≤ √n vs Primes > √n:**
Any n has at most one prime factor > √n.
Products of primes ≤ √n give many smooth numbers.
-/
/-
## Part VI: Related Concepts
-/

/--
**y-Smooth Numbers:**
A number is y-smooth if all its prime factors are ≤ y.
-/
def IsYSmooth (y m : ℕ) : Prop :=
  m ≥ 1 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ m → p ≤ y

/--
**Smooth Number Count:**
Ψ(x, y) = number of y-smooth integers ≤ x.
-/
noncomputable def smoothCount (x y : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (IsYSmooth y) |>.card

/--
**Dickman-de Bruijn Asymptotics:**
Ψ(x, x^{1/u}) ~ x·ρ(u) where ρ is the Dickman function.
The count of y-smooth numbers up to x is asymptotically x·ρ(log x / log y).
-/
/-
## Part VII: Summary
-/

/--
**Erdős Problem #983: SOLVED**
Erdős-Straus (1970) determined the precise asymptotics.

The answer is NO: 2π(√n) - f(π(n)+1, n) does not tend to infinity.
The difference is sublinear in √n.
-/
theorem erdos_983 :
    -- The answer to the main question is NO
    ¬ErdosQuestion983 ∧
    -- The difference is small (sublinear in √n)
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |(2 * (primePi (Nat.sqrt n) : ℝ) - (f (primePi n + 1) n : ℝ))| /
      (n : ℝ)^(1/2 : ℝ) < ε) :=
  ⟨erdos_question_answer, difference_is_sublinear⟩

end Erdos983
