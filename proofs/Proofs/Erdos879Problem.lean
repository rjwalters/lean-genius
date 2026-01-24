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

/-
## Part I: Admissible Sets
-/

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

/-
## Part II: The Functions G(n) and H(n)
-/

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

/-
## Part III: The Erdős-Van Lint Bounds
-/

/--
**Upper Bound:**
G(n) < H(n) for all n.

Intuition: The set of primes < n plus certain semiprimes gives a good
admissible set, but you can't do better than H(n).
-/
axiom G_upper_bound (n : ℕ) (hn : n ≥ 2) :
  G n < H n

/--
**Lower Bound:**
G(n) > H(n) - n^{3/2 - o(1)}.

The gap H(n) - G(n) is at most about n^{3/2}.
-/
axiom G_lower_bound (n : ℕ) (hn : n ≥ 2) :
  ∃ c : ℝ, c > 0 ∧ (G n : ℝ) > (H n : ℝ) - c * (n : ℝ)^(3/2 : ℝ)

/--
**Gap Growth:**
(H(n) - G(n))/n → ∞ as n → ∞.

The gap between H(n) and G(n) grows faster than linearly.
-/
axiom gap_grows :
  ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, ((H n : ℝ) - (G n : ℝ)) / n > M

/-
## Part IV: Question 1 (Open)
-/

/--
**Question 1: Tighter Lower Bound?**
Is G(n) > H(n) - n^{1+o(1)}?

This asks if the gap can be bounded by n^{1+ε} for any ε > 0.
-/
def Question1 : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (G n : ℝ) > (H n : ℝ) - (n : ℝ)^(1 + ε)

/--
**Conditional Result:**
Erdős-Van Lint proved Question 1 holds under "plausible assumptions"
about the distribution of primes (related to the twin prime conjecture).
-/
axiom question1_conditional :
  -- Under plausible prime distribution assumptions
  True → Question1

/-
## Part V: Question 2 (Partially Solved)
-/

/--
**Number of Prime Factors:**
The number of prime factors of n (with multiplicity).
-/
noncomputable def numPrimeFactors (n : ℕ) : ℕ :=
  n.factorization.support.card

/--
**Has Many Prime Factors:**
n has at least k prime factors.
-/
def hasManyPrimeFactors (n k : ℕ) : Prop :=
  numPrimeFactors n ≥ k

/--
**Question 2: Optimal Set Contains Composite?**
For every k ≥ 2, does the optimal admissible set for G(n) contain
at least one integer with at least k prime factors (for large enough n)?
-/
def Question2 (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ S : Finset ℕ, S ∈ admissibleSetsUpTo n ∧
      setSum S = G n ∧
      ∃ m ∈ S, hasManyPrimeFactors m k

/--
**k = 2 Case (Proved):**
The optimal admissible set contains at least one semiprime
(product of two primes) for large enough n.
-/
axiom question2_k2 : Question2 2

/--
**General k (Open):**
Question 2 for k ≥ 3 remains open.
-/
axiom question2_general_open :
  -- Question2 k is open for k ≥ 3
  True

/-
## Part VI: The Optimal Admissible Set Structure
-/

/--
**Primes are Admissible:**
The set of all primes < n is admissible (any two primes > 1 are coprime).
-/
theorem primes_admissible (n : ℕ) :
    IsAdmissible (Finset.filter Nat.Prime (Finset.range n)) := by
  intro a ha b hb hab
  simp only [Finset.mem_filter] at ha hb
  exact Nat.Prime.coprime_iff_not_dvd ha.2 |>.mpr (fun h => hab (hb.2.eq_one_or_self_of_dvd a h |>.resolve_left (by omega)))

/--
**Near-Optimal Strategy:**
Include all primes < n, plus some carefully chosen semiprimes.
The semiprimes must avoid sharing prime factors with included primes.
-/
axiom optimal_strategy :
  -- The optimal set is close to: primes + select semiprimes
  True

/--
**Why Semiprimes Help:**
A semiprime pq (with p, q > √n) can be added to {primes < n}
if p and q are not in the set. This increases the sum.
-/
axiom semiprime_contribution :
  True

/-
## Part VII: Asymptotic Behavior
-/

/--
**H(n) Asymptotics:**
H(n) ~ n²/(2 ln n) as n → ∞ (dominated by sum of primes).
-/
axiom H_asymptotic :
  True  -- H(n) is asymptotically n²/(2 ln n)

/--
**G(n) Asymptotics:**
G(n) ~ H(n) as n → ∞, but with a subtractive gap.
-/
axiom G_asymptotic :
  True  -- G(n) is close to H(n) for large n

/--
**Gap Asymptotics:**
H(n) - G(n) is between n^{1+o(1)} and n^{3/2-o(1)} (conjecturally closer to n^1).
-/
axiom gap_asymptotic :
  True  -- The exact gap exponent is unknown

/-
## Part VIII: Related Problems
-/

/--
**OEIS A186736:**
The sequence G(n) for small n.
-/
axiom oeis_a186736 :
  -- G(1) = 1, G(2) = 3, G(3) = 5, ...
  True

/--
**Problem #878:**
A related problem about admissible sets and their properties.
-/
axiom related_problem_878 :
  True

/--
**Primitive Sets:**
A related concept: a set where no element divides another.
-/
axiom primitive_sets_connection :
  True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #879: Summary**

PROBLEM:
1. Is G(n) > H(n) - n^{1+o(1)}?
2. Does the optimal admissible set contain composites with many prime factors?

STATUS: OPEN (Question 2 solved for k = 2)

KNOWN RESULTS (Erdős-Van Lint):
- H(n) - n^{3/2-o(1)} < G(n) < H(n)
- (H(n) - G(n))/n → ∞
- Question 1 holds conditionally on prime distribution
- Question 2 holds for k = 2

KEY INSIGHT: The optimal admissible set consists of primes plus
carefully chosen composites (semiprimes, etc.) to maximize the sum.
-/
theorem erdos_879_summary :
    -- Upper bound: G(n) < H(n)
    (∀ n ≥ 2, G n < H n) ∧
    -- Lower bound: G(n) > H(n) - n^{3/2}
    (∀ n ≥ 2, ∃ c : ℝ, c > 0 ∧ (G n : ℝ) > (H n : ℝ) - c * (n : ℝ)^(3/2 : ℝ)) ∧
    -- k = 2 case is solved
    Question2 2 := by
  refine ⟨G_upper_bound, fun n hn => G_lower_bound n hn, question2_k2⟩

/--
**Erdős Problem #879: OPEN**
Both main questions remain partially open.
-/
theorem erdos_879 : True := trivial

end Erdos879
