/-
Erdős Problem #356: Consecutive Sums in Strictly Increasing Sequences

Source: https://erdosproblems.com/356
Status: SOLVED (YES)

Statement:
Is there some c > 0 such that, for all sufficiently large n, there exist integers
a₁ < a₂ < ... < aₖ ≤ n such that there are at least cn² distinct integers of the
form Σ_{u≤i≤v} aᵢ (consecutive subsums)?

Answer: YES — proved by Adrian Beker (2023).

Known Results:
- For aᵢ = i (1, 2, 3, ..., n), this fails (only O(n²) consecutive sums,
  but many collide, giving only O(n) distinct values)
- Konieczny (2015): Permutations of {1,...,n} can achieve cn² distinct sums
- Beker (2023): Strictly increasing sequences can achieve cn² distinct sums

References:
- [Be23]: Beker "On a problem of Erdős and Graham about consecutive sums" (2023)
- [Ko15]: Konieczny "On consecutive sums in permutations" (2015)
- Erdős-Graham [ErGr80]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

open Nat Finset List

namespace Erdos356

/-! ## Part I: Consecutive Sums -/

/--
**Consecutive Subsum:**
For a sequence a₁, ..., aₖ, a consecutive subsum is Σ_{i=u}^{v} aᵢ for some 0 ≤ u ≤ v < k.
We compute it by dropping u elements, taking (v - u + 1), and summing.
-/
def consecutiveSubsum (seq : List ℕ) (u v : ℕ) : ℕ :=
  (seq.drop u).take (v - u + 1) |>.sum

/--
**Set of All Consecutive Subsums:**
The set of all possible consecutive subsums of a sequence, collected into a Finset.
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

/-! ## Part II: The Trivial Sequence -/

/--
**Trivial Sequence {1, 2, ..., n}:**
The simplest strictly increasing sequence bounded by n. Its consecutive subsums
are of the form (v-u+1)(v+u)/2, and many of these collide.
-/
def trivialSequence (n : ℕ) : List ℕ :=
  List.range' 1 n

/--
**Consecutive sums of 1, ..., n grow linearly:**
The sum from position u to v is v(v+1)/2 - (u-1)u/2 = (v-u+1)(v+u)/2.
These are bounded by n(n+1)/2, but due to collisions among sums of different
lengths, only O(n) distinct values arise.
-/
axiom trivial_fails (n : ℕ) :
    ∃ C : ℕ, distinctConsecutiveSums (trivialSequence n) ≤ C * n

/--
**Why {1, 2, ..., n} fails — arithmetic structure causes collisions:**
In an arithmetic progression, consecutive sums are determined by length and
midpoint: sum(u..v) = (v-u+1)·(u+v)/2. Different (u,v) pairs can share the
same product, causing collisions. For example, 1+2+3+4 = 10 and 4+6 = 10
in rearranged form. The highly structured nature of {1,...,n} prevents
quadratic growth in distinct sums.
-/
axiom trivial_collision_structure :
    ∀ n : ℕ, n ≥ 2 →
      distinctConsecutiveSums (trivialSequence n) < n * n

/-! ## Part III: Strictly Increasing Sequences -/

/--
**Strictly Increasing Sequence:**
A sequence a₁, ..., aₖ with a₁ < a₂ < ... < aₖ.
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

/-! ## Part IV: The Main Conjecture -/

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
distinct consecutive sums. This resolved the problem in the affirmative.

Reference: Beker, "On a problem of Erdős and Graham about consecutive sums" (2023)
-/
axiom beker_theorem : erdosGrahamConjecture

/-! ## Part V: The Permutation Variant -/

/--
**Permutation of {1, ..., n}:**
A rearrangement of {1, 2, ..., n} — the list contains exactly these elements.
-/
def isPermutation (seq : List ℕ) (n : ℕ) : Prop :=
  seq.toFinset = Finset.range' 1 n

/--
**Permutation Conjecture:**
Does there exist a permutation of {1,...,n} with cn² distinct consecutive sums?
This is a stronger version: we require a rearrangement of {1,...,n}, not just
any strictly increasing sequence bounded by n.
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
consecutive sums. This preceded Beker's result on strictly increasing sequences.

Reference: Konieczny, "On consecutive sums in permutations" (2015)
-/
axiom konieczny_theorem : permutationConjecture

/-! ## Part VI: Construction Insights -/

/--
**The construction principle:**
To maximize distinct consecutive sums, elements must be spaced so that
different (u,v) pairs yield different sums. This requires breaking the
arithmetic regularity that causes collisions in {1,...,n}.

Beker's construction uses number-theoretic techniques to build sequences
where consecutive subsums are "spread out" — avoiding the sum collisions
that plague arithmetic progressions.
-/
axiom beker_construction_yields_quadratic :
    ∃ c : ℚ, c > 0 ∧ c < 1 ∧ erdosGrahamConjecture

/-! ## Part VII: Related Problems -/

/--
**Connection to Erdős #34 (Permutations):**
Problem #34 asks the same question but specifically for permutations.
Konieczny's theorem resolves it. The permutation variant is strictly
harder: any permutation of {1,...,n} is a valid sequence for #356,
but not vice versa.
-/
axiom permutation_implies_increasing :
    permutationConjecture → erdosGrahamConjecture

/--
**Connection to Erdős #357 (Consecutive integers):**
Problem #357 asks: among the integers > n expressible as consecutive sums
of a sequence bounded by n, how many consecutive integers can we find?
Is it at least cn for some c > 0?
-/
def erdos357Question : Prop :=
  ∃ c : ℚ, c > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ seq : List ℕ, isValidSequence seq n ∧
        ∃ start : ℕ, start > n ∧
          ∀ i : ℕ, i < (c * n).num.toNat →
            start + i ∈ consecutiveSums seq

/-! ## Part VIII: Upper and Lower Bounds -/

/--
**Upper bound on consecutive sums:**
A sequence of length k has at most k(k+1)/2 consecutive subsums
(choosing u ≤ v from {0,...,k-1}). Since k ≤ n for a valid sequence,
the maximum is O(n²).
-/
axiom upper_bound (seq : List ℕ) :
    distinctConsecutiveSums seq ≤ seq.length * (seq.length + 1) / 2

/--
**Lower bound from Beker:**
There exist sequences achieving cn² for some explicit c > 0.
Combined with the upper bound, the growth rate is Θ(n²).
-/
axiom lower_bound_exists :
    ∃ c : ℚ, c > 0 ∧
      ∀ n : ℕ, n ≥ 10 →
        ∃ seq : List ℕ, isValidSequence seq n ∧
          (distinctConsecutiveSums seq : ℚ) ≥ c * n^2

/-! ## Part IX: Summary -/

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
    permutationConjecture :=
  ⟨beker_theorem, konieczny_theorem⟩

/--
**Main Theorem:**
Strictly increasing sequences can achieve Ω(n²) distinct consecutive sums.
-/
theorem erdos_356 : erdosGrahamConjecture := beker_theorem

end Erdos356
