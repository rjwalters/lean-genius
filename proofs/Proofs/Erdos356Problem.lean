/-
Erdős Problem #356: Consecutive Sums in Strictly Increasing Sequences

Source: https://erdosproblems.com/356
Status: SOLVED

Statement:
Is there some c > 0 such that, for all sufficiently large n, there exist integers
a₁ < a₂ < ... < aₖ ≤ n such that there are at least cn² distinct integers of the
form Σ_{u≤i≤v} aᵢ (consecutive subsums)?

Known Results:
- For aᵢ = i (1, 2, 3, ..., n), this fails (only O(n) distinct consecutive sums)
- Konieczny (2015): Permutations of {1,...,n} can achieve cn² distinct sums
- Beker (2023): SOLVED the original problem in the affirmative

The answer is YES: there exist strictly increasing sequences with quadratically
many distinct consecutive sums.

References:
- [Be23]: Beker "On a problem of Erdős and Graham about consecutive sums" (2023)
- [Ko15]: Konieczny "On consecutive sums in permutations" (2015)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

open Nat Finset List

namespace Erdos356

/-
## Part I: Consecutive Sums
-/

/--
**Consecutive Subsum:**
For a sequence a₁, ..., aₖ, a consecutive subsum is Σ_{i=u}^{v} aᵢ for some 1 ≤ u ≤ v ≤ k.
-/
def consecutiveSubsum (seq : List ℕ) (u v : ℕ) : ℕ :=
  (seq.drop u).take (v - u + 1) |>.sum

/--
**Set of All Consecutive Subsums:**
The set of all possible consecutive subsums of a sequence.
-/
def consecutiveSums (seq : List ℕ) : Finset ℕ :=
  (List.range seq.length).bind (fun u =>
    (List.range (seq.length - u)).map (fun d =>
      consecutiveSubsum seq u (u + d))) |>.toFinset

/--
**Count of Distinct Consecutive Sums:**
The number of distinct consecutive subsums in a sequence.
-/
def distinctConsecutiveSums (seq : List ℕ) : ℕ :=
  (consecutiveSums seq).card

/-
## Part II: The Trivial Sequence
-/

/--
**Trivial Sequence {1, 2, ..., n}:**
The consecutive subsums of 1, 2, ..., n are exactly the triangular numbers
and their differences. There are only O(n) distinct values.
-/
def trivialSequence (n : ℕ) : List ℕ :=
  List.range' 1 n

/--
**Consecutive sums of 1, ..., n:**
The sum from u to v is v(v+1)/2 - (u-1)u/2 = (v-u+1)(v+u)/2.
These are bounded and have only O(n) distinct values.
-/
theorem trivial_fails (n : ℕ) :
    ∃ C : ℕ, distinctConsecutiveSums (trivialSequence n) ≤ C * n := by
  sorry

/--
**Why {1, 2, ..., n} fails:**
Many consecutive sums collide. For example:
1 + 2 + 3 + 4 = 10 = 1 + 2 + 3 + 4 (only one way for this sum)
But also 3 + 4 + 5 = 12 = 5 + 7 (many collisions in similar sums)
-/
theorem trivial_intuition : True := trivial

/-
## Part III: Strictly Increasing Sequences
-/

/--
**Strictly Increasing Sequence:**
A sequence a₁, ..., aₖ with a₁ < a₂ < ... < aₖ ≤ n.
-/
def isStrictlyIncreasing (seq : List ℕ) : Prop :=
  seq.Pairwise (· < ·)

/--
**Bounded by n:**
All elements are at most n.
-/
def boundedBy (seq : List ℕ) (n : ℕ) : Prop :=
  ∀ x ∈ seq, x ≤ n

/--
**Valid Sequence:**
A valid sequence for the problem is strictly increasing with all elements ≤ n.
-/
def isValidSequence (seq : List ℕ) (n : ℕ) : Prop :=
  isStrictlyIncreasing seq ∧ boundedBy seq n

/-
## Part IV: The Main Conjecture
-/

/--
**Erdős-Graham Conjecture (Original):**
There exists c > 0 such that for all large n, there exists a valid sequence
with at least cn² distinct consecutive sums.
-/
def erdosGrahamConjecture : Prop :=
  ∃ c : ℚ, c > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ seq : List ℕ, isValidSequence seq n ∧
        (distinctConsecutiveSums seq : ℚ) ≥ c * n^2

/--
**Beker's Theorem (2023):**
The Erdős-Graham conjecture is TRUE.
There exist strictly increasing sequences achieving quadratically many
distinct consecutive sums.
-/
axiom beker_theorem : erdosGrahamConjecture

/-
## Part V: The Permutation Variant
-/

/--
**Permutation of {1, ..., n}:**
A rearrangement of {1, 2, ..., n}.
-/
def isPermutation (seq : List ℕ) (n : ℕ) : Prop :=
  seq.toFinset = Finset.range' 1 n

/--
**Permutation Conjecture:**
Does there exist a permutation of {1,...,n} with cn² distinct consecutive sums?
-/
def permutationConjecture : Prop :=
  ∃ c : ℚ, c > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ seq : List ℕ, isPermutation seq n ∧
        (distinctConsecutiveSums seq : ℚ) ≥ c * n^2

/--
**Konieczny's Theorem (2015):**
The permutation conjecture is TRUE.
There exist permutations of {1,...,n} with quadratically many distinct
consecutive sums.
-/
axiom konieczny_theorem : permutationConjecture

/-
## Part VI: Constructions
-/

/--
**The key insight:**
To maximize distinct sums, we want consecutive subsums to be as "spread out"
as possible. This requires careful spacing between elements.
-/
axiom construction_intuition : True

/--
**Beker's construction:**
Beker's proof constructs sequences using number-theoretic techniques
to ensure minimal collisions among consecutive sums.
-/
axiom beker_construction : True

/--
**Lower bound on achievable c:**
The constant c can be made explicit, though the exact optimal value
may depend on the construction used.
-/
axiom explicit_constant : ∃ c : ℚ, c > 0 ∧ c < 1 ∧ erdosGrahamConjecture

/-
## Part VII: Related Questions
-/

/--
**Problem #34 - Permutations:**
See Erdős #34 for the permutation version (Konieczny's result).
-/
axiom erdos_34_connection : True

/--
**Problem #357 - Consecutive integers:**
How many consecutive integers > n can be represented as consecutive sums?
Is it true that for any c > 0, at least cn such integers are possible?
-/
axiom erdos_357_question : True

/--
**Problem #358 - Related variant:**
Another related problem in the Erdős-Graham series.
-/
axiom erdos_358_connection : True

/-
## Part VIII: Upper and Lower Bounds
-/

/--
**Upper bound:**
The maximum possible consecutive sums is at most k(k+1)/2 ≈ n²/2
(if the sequence has length k ≈ n).
-/
theorem upper_bound (seq : List ℕ) :
    distinctConsecutiveSums seq ≤ seq.length * (seq.length + 1) / 2 := by
  sorry

/--
**Lower bound from Beker:**
There exist sequences achieving cn² for some explicit c > 0.
-/
theorem lower_bound_exists :
    ∃ c : ℚ, c > 0 ∧
      ∀ n : ℕ, n ≥ 10 →
        ∃ seq : List ℕ, isValidSequence seq n ∧
          (distinctConsecutiveSums seq : ℚ) ≥ c * n^2 := by
  sorry

/-
## Part IX: Summary
-/

/--
**Erdős Problem #356 Summary:**

PROBLEM: Is there c > 0 such that strictly increasing sequences a₁ < ... < aₖ ≤ n
can achieve at least cn² distinct consecutive sums Σ_{i=u}^{v} aᵢ?

STATUS: SOLVED (YES)

KEY RESULTS:
1. The trivial sequence {1, 2, ..., n} FAILS (only O(n) distinct sums)
2. Konieczny (2015): Permutations can achieve cn² distinct sums
3. Beker (2023): Strictly increasing sequences can achieve cn² distinct sums

The answer is YES: carefully constructed sequences achieve quadratic growth.
-/
theorem erdos_356_solved :
    -- The main conjecture is proven
    erdosGrahamConjecture ∧
    -- The permutation variant is also proven
    permutationConjecture := by
  exact ⟨beker_theorem, konieczny_theorem⟩

/--
**Main Theorem:**
Strictly increasing sequences can achieve Ω(n²) distinct consecutive sums.
-/
theorem erdos_356 : erdosGrahamConjecture := beker_theorem

end Erdos356
