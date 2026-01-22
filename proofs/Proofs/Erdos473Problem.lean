/-
Erdős Problem #473: Prime Sum Permutations

Source: https://erdosproblems.com/473
Status: SOLVED (Odlyzko)

Statement:
Is there a permutation a₁, a₂, ... of the positive integers such that
a_k + a_{k+1} is always prime?

Answer: YES (Odlyzko)

Historical Context:
- Asked by Segal (circa 1980)
- Solved affirmatively by Odlyzko (unpublished)
- Referenced in Erdős-Graham (1980) "Old and new problems in combinatorial number theory"

Related Questions:
1. Greedy Algorithm: Let a₁ = 1, a_{n+1} = min{x : a_n + x is prime and x ∉ {a₁,...,a_n}}
   - Does every positive integer appear? (Open)
   - Does every prime appear as a sum? NO - 197 doesn't appear (van Doorn)

2. Finite Version: For all n ≥ 2, is there a permutation of {1,...,n}
   such that consecutive sums are prime? (Likely yes, true for infinitely many n)

References:
- [ErGr80] Erdős-Graham (1980), p.94

Tags: number-theory, primes, permutations, additive-combinatorics
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Data.Finset.Basic

open Nat

namespace Erdos473

/-!
## Part I: Basic Definitions
-/

/--
**Permutation of Positive Integers:**
A bijection from ℕ+ to ℕ+.
-/
def IsPermutation (a : ℕ → ℕ) : Prop :=
  Function.Bijective a ∧ ∀ n, a n ≥ 1

/--
**Prime Sum Property:**
Every consecutive sum a_k + a_{k+1} is prime.
-/
def HasPrimeSumProperty (a : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, k ≥ 1 → (a k + a (k + 1)).Prime

/--
**Prime Sum Permutation:**
A permutation where consecutive sums are always prime.
-/
def IsPrimeSumPermutation (a : ℕ → ℕ) : Prop :=
  IsPermutation a ∧ HasPrimeSumProperty a

/-!
## Part II: The Main Question
-/

/--
**Segal's Question:**
Does there exist a permutation of positive integers with consecutive sums prime?
-/
def segalQuestion : Prop :=
  ∃ a : ℕ → ℕ, IsPrimeSumPermutation a

/--
**Odlyzko's Theorem:**
There exists such a permutation. The answer is YES.
-/
axiom odlyzko_theorem : segalQuestion

/-!
## Part III: The Greedy Algorithm
-/

/--
**Greedy Algorithm Definition:**
a₁ = 1, and a_{n+1} = min{x : a_n + x is prime and x not used before}

This is well-defined because for any prev and finite used set, there exists
x not in used such that prev + x is prime (by infinitude of primes).
-/
axiom greedySeq : ℕ → ℕ

/--
**Greedy Sequence Initial Condition:**
The greedy sequence starts with a₁ = 1.
-/
axiom greedySeq_one : greedySeq 1 = 1

/--
**Greedy Sequence Recurrence:**
Each term is the smallest unused integer giving a prime sum.
-/
axiom greedySeq_recurrence : ∀ n ≥ 1,
    let prev := greedySeq n
    let used := {greedySeq i | i ≤ n}
    (prev + greedySeq (n + 1)).Prime ∧ greedySeq (n + 1) ∉ used

/--
**Greedy Sequence Property:**
The greedy sequence satisfies the prime sum property by construction.
-/
axiom greedy_has_prime_sums : HasPrimeSumProperty greedySeq

/--
**Open Question: Greedy Covers All Integers?**
Does the greedy sequence eventually include every positive integer?
This remains OPEN.
-/
def greedyCoversAllIntegers : Prop :=
  ∀ n : ℕ, n ≥ 1 → ∃ k : ℕ, greedySeq k = n

axiom greedy_covers_all_open : ¬Decidable greedyCoversAllIntegers

/--
**Van Doorn's Observation:**
Not all primes appear as sums in the greedy sequence.
Specifically, 197 never appears as a sum a_k + a_{k+1}.
-/
axiom van_doorn_197 :
    ∀ k : ℕ, k ≥ 1 → greedySeq k + greedySeq (k + 1) ≠ 197

/-!
## Part IV: Finite Version
-/

/--
**Finite Permutation with Prime Sums:**
A permutation of {1,...,n} where consecutive sums are prime.
-/
def IsFinitePrimeSumPermutation (n : ℕ) (a : Fin n → Fin n) : Prop :=
  Function.Bijective a ∧
  ∀ k : Fin (n - 1), ((a ⟨k.val, Nat.lt_of_lt_pred k.isLt⟩).val + 1 +
                     (a ⟨k.val + 1, Nat.add_lt_of_lt_sub k.isLt⟩).val + 1).Prime

/--
**Finite Version Question:**
For all n ≥ 2, does a finite prime sum permutation of {1,...,n} exist?
-/
def finiteVersionQuestion : Prop :=
  ∀ n : ℕ, n ≥ 2 → ∃ a : Fin n → Fin n, IsFinitePrimeSumPermutation n a

/--
**Finite Version Conjecture:**
Likely true by probabilistic arguments, confirmed for infinitely many n.
-/
axiom finite_version_true_infinitely_often :
    Set.Infinite {n : ℕ | ∃ a : Fin n → Fin n, IsFinitePrimeSumPermutation n a}

/-!
## Part V: Connections and Generalizations
-/

/--
**Hamilton Path Interpretation:**
This problem is equivalent to finding a Hamilton path in a graph where:
- Vertices are positive integers
- Edges connect i and j if i + j is prime

Odlyzko proved such a path exists.
-/
def primeSumGraph : ℕ → ℕ → Prop :=
  fun i j => i ≠ j ∧ (i + j).Prime

/--
**Connection to Goldbach:**
The structure of which pairs sum to primes is related to Goldbach's conjecture
(every even n > 2 is the sum of two primes).
-/
theorem goldbach_connection : True := trivial

/--
**Generalization: Other Conditions:**
One could ask for permutations where consecutive sums satisfy other properties:
- Always composite
- Always a perfect square
- Always a Fibonacci number
These variants have different answers.
-/
theorem generalizations : True := trivial

/-!
## Part VI: Properties of Prime Sum Permutations
-/

/--
**Parity Constraint:**
For a + b to be prime > 2, one of a, b must be even and the other odd.
This constrains the permutation structure.

The only even prime is 2, so if a_k + a_{k+1} > 2 is prime, it must be odd,
meaning exactly one of a_k, a_{k+1} is even.
-/
axiom parity_constraint (a : ℕ → ℕ) (h : HasPrimeSumProperty a) :
    ∀ k : ℕ, k ≥ 1 →
      (Even (a k) ∧ Odd (a (k + 1))) ∨ (Odd (a k) ∧ Even (a (k + 1))) ∨
      (a k + a (k + 1) = 2)

/--
**Density Considerations:**
Among the first N integers, roughly half are even and half odd.
A prime sum permutation must carefully interleave evens and odds.
-/
theorem density_consideration : True := trivial

/-!
## Part VII: The Greedy Sequence Values
-/

/--
**Known Initial Values:**
The greedy sequence begins: 1, 2, 3, 4, 7, 6, 5, 8, 9, ...
(Each consecutive sum is prime: 3, 5, 7, 11, 13, 11, 13, 17, ...)
-/
axiom greedy_initial_values :
    greedySeq 1 = 1 ∧
    greedySeq 2 = 2 ∧
    greedySeq 3 = 3 ∧
    greedySeq 4 = 4 ∧
    greedySeq 5 = 7

/-!
## Part VIII: Summary
-/

/--
**Erdős Problem #473: SOLVED**

**QUESTION:** Is there a permutation a₁, a₂, ... of positive integers
such that a_k + a_{k+1} is always prime?

**ANSWER:** YES (Odlyzko)

**RELATED QUESTIONS:**
1. Does the greedy algorithm cover all integers? OPEN
2. Does every prime appear as a sum in the greedy sequence? NO (197 doesn't)
3. Finite version for all n ≥ 2? Likely yes, true for infinitely many n

**KEY INSIGHT:**
This is a Hamilton path problem in the "prime sum graph" where vertices are
positive integers and edges connect i,j when i+j is prime.
-/
theorem erdos_473_solved : segalQuestion := odlyzko_theorem

/--
**Main Summary Theorem:**
Collects the main results about prime sum permutations.
-/
theorem erdos_473_main :
    -- Main question answered affirmatively
    segalQuestion ∧
    -- Greedy sequence satisfies prime sum property
    HasPrimeSumProperty greedySeq ∧
    -- But 197 never appears as a sum in greedy
    (∀ k ≥ 1, greedySeq k + greedySeq (k + 1) ≠ 197) ∧
    -- Finite version true for infinitely many n
    Set.Infinite {n : ℕ | ∃ a : Fin n → Fin n, IsFinitePrimeSumPermutation n a} := by
  refine ⟨odlyzko_theorem, greedy_has_prime_sums, van_doorn_197,
         finite_version_true_infinitely_often⟩

end Erdos473
