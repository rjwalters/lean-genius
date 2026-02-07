/-
Erdős Problem #879: Maximum Sum of Pairwise Coprime Sets

Source: https://erdosproblems.com/879
Status: OPEN

Statement:
Call a set S ⊆ {1,...,n} admissible if (a,b) = 1 for all distinct a, b ∈ S
(pairwise coprime). Define:
  G(n) = max_S Σ_{a ∈ S} a  (maximum sum over admissible sets)
  H(n) = Σ_{p < n} p + n·π(√n)  (sum of primes + adjustment)

Questions:
1. Is G(n) > H(n) - n^{1+o(1)}?
2. For every k ≥ 2, does the optimal admissible set contain at least one
   integer with ≥ k prime factors (for large enough n)?

Known Results (Erdős-Van Lint):
- H(n) - n^{3/2-o(1)} < G(n) < H(n)
- (H(n) - G(n))/n → ∞
- Question 1 holds under plausible assumptions about prime distribution
- Question 2 proved for k = 2

References:
- [Er84e], [Er98]
- Related: Problem #878
- OEIS: A186736
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction

open Nat Finset BigOperators

namespace Erdos879

/- ## Part I: Admissible Sets -/

/--
**Pairwise Coprime (Admissible):**
A set S is admissible if gcd(a, b) = 1 for all distinct a, b ∈ S.
-/
def IsAdmissible (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

/--
**The Sum of a Set:**
The sum of all elements in a finite set S.
-/
def setSum (S : Finset ℕ) : ℕ := ∑ a ∈ S, a

/--
**Admissible Subsets of {1, ..., n}:**
The collection of all admissible subsets of {1, ..., n}.
-/
def admissibleSetsUpTo (n : ℕ) : Set (Finset ℕ) :=
  {S | S ⊆ Finset.range (n + 1) ∧ IsAdmissible S}

/- ## Part II: The Functions G(n) and H(n) -/

/--
**G(n): Maximum Sum of Admissible Sets**
The maximum sum over all admissible subsets of {1, ..., n}.
-/
noncomputable def G (n : ℕ) : ℕ :=
  sSup {setSum S | S ∈ admissibleSetsUpTo n}

/--
**Prime Counting Function:**
π(x) = number of primes ≤ x.
-/
noncomputable def primeCountingFn (x : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range (x + 1))).card

/--
**Sum of Primes Below n:**
Σ_{p < n, p prime} p
-/
noncomputable def sumOfPrimes (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range n), p

/--
**H(n): The Comparison Function**
H(n) = Σ_{p < n} p + n · π(√n)
-/
noncomputable def H (n : ℕ) : ℕ :=
  sumOfPrimes n + n * primeCountingFn (Nat.sqrt n)

/- ## Part III: The Erdős-Van Lint Bounds -/

/--
**Upper Bound (Erdős-Van Lint):**
G(n) < H(n) for all n ≥ 2. The set of primes plus semiprimes cannot
exceed H(n) in total sum.
-/
axiom G_upper_bound (n : ℕ) (hn : n ≥ 2) :
  G n < H n

/--
**Lower Bound (Erdős-Van Lint):**
G(n) > H(n) - c·n^{3/2} for some constant c > 0. The gap between
H(n) and G(n) is at most of order n^{3/2}.
-/
axiom G_lower_bound (n : ℕ) (hn : n ≥ 2) :
  ∃ c : ℝ, c > 0 ∧ (G n : ℝ) > (H n : ℝ) - c * (n : ℝ)^(3/2 : ℝ)

/--
**Gap Growth (Erdős-Van Lint):**
(H(n) - G(n))/n → ∞ as n → ∞. The gap grows faster than linearly,
so G(n) is genuinely smaller than H(n) by more than O(n).
-/
axiom gap_grows :
  ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, ((H n : ℝ) - (G n : ℝ)) / n > M

/- ## Part IV: Question 1 (Open) -/

/--
**Question 1: Tighter Lower Bound?**
Is G(n) > H(n) - n^{1+o(1)}? This asks if the gap can be bounded
by n^{1+ε} for any ε > 0, improving the known n^{3/2} bound.
-/
def Question1 : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (G n : ℝ) > (H n : ℝ) - (n : ℝ)^(1 + ε)

/- ## Part V: Question 2 (Partially Solved) -/

/--
**Number of Distinct Prime Factors:**
The number of distinct prime factors of n (ω(n) in standard notation).
-/
noncomputable def numPrimeFactors (n : ℕ) : ℕ :=
  n.factorization.support.card

/--
**Has At Least k Prime Factors:**
n has at least k distinct prime factors.
-/
def hasManyPrimeFactors (n k : ℕ) : Prop :=
  numPrimeFactors n ≥ k

/--
**Question 2: Optimal Set Contains Composite?**
For every k ≥ 2, does the optimal admissible set for G(n) contain
at least one integer with at least k distinct prime factors (for large enough n)?
-/
def Question2 (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ S : Finset ℕ, S ∈ admissibleSetsUpTo n ∧
      setSum S = G n ∧
      ∃ m ∈ S, hasManyPrimeFactors m k

/--
**k = 2 Case (Proved by Erdős-Van Lint):**
The optimal admissible set contains at least one semiprime
(product of two distinct primes) for sufficiently large n.
-/
axiom question2_k2 : Question2 2

/- ## Part VI: The Optimal Admissible Set Structure -/

/--
**Primes are Admissible:**
The set of all primes < n is admissible, since distinct primes are coprime.
This provides a natural baseline admissible set whose sum is close to G(n).
-/
theorem primes_admissible (n : ℕ) :
    IsAdmissible (Finset.filter Nat.Prime (Finset.range n)) := by
  intro a ha b hb hab
  simp only [Finset.mem_filter] at ha hb
  exact Nat.Prime.coprime_iff_not_dvd ha.2 |>.mpr
    (fun h => hab (hb.2.eq_one_or_self_of_dvd a h |>.resolve_left (by omega)))

/- ## Part VII: Summary -/

/--
**Erdős Problem #879: Summary**

Combines the three main known results of Erdős-Van Lint:
1. Upper bound: G(n) < H(n) for all n ≥ 2
2. Lower bound: G(n) > H(n) - c·n^{3/2} for some c > 0
3. Question 2 for k = 2: optimal sets contain semiprimes
-/
theorem erdos_879_summary :
    (∀ n ≥ 2, G n < H n) ∧
    (∀ n ≥ 2, ∃ c : ℝ, c > 0 ∧ (G n : ℝ) > (H n : ℝ) - c * (n : ℝ)^(3/2 : ℝ)) ∧
    Question2 2 :=
  ⟨G_upper_bound, fun n hn => G_lower_bound n hn, question2_k2⟩

end Erdos879
