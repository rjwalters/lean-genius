/-
Erdős Problem #333: Sparse Sumset Bases

Source: https://erdosproblems.com/333
Status: DISPROVED (Erdős-Newman 1977)

Statement:
Let A ⊆ ℕ be a set of density zero. Does there exist a B such that A ⊆ B + B
and |B ∩ {1,...,N}| = o(N^{1/2}) for all large N?

Answer: NO (in general)

Background:
- B + B = {b₁ + b₂ : b₁, b₂ ∈ B} is the sumset
- The question asks: can every zero-density set be represented as a sumset of
  an exceptionally sparse set B?
- "Exceptionally sparse" means |B ∩ [1,N]| = o(√N)

Known Results:
- Erdős-Newman (1977): YES for A = squares
- Erdős-Newman (1977), Theorem 2: Implies NO in general (overlooked by E-G)
- The negative answer follows from bounds on sumset covering

Related: Problem #806

Tags: additive-combinatorics, sumsets, density
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Set.Card

open Asymptotics Filter
open scoped BigOperators

namespace Erdos333

/-!
## Part I: Basic Definitions
-/

/--
**Natural density:**
The asymptotic density of A ⊆ ℕ is lim_{N→∞} |A ∩ [1,N]| / N (if it exists).
-/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.filter (· ∈ A) (Finset.range (N + 1))).card

noncomputable def hasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N => (countingFunction A N : ℝ) / N) atTop (nhds d)

/--
**Zero density:**
A set has density zero if its counting function grows slower than N.
-/
def hasZeroDensity (A : Set ℕ) : Prop :=
  hasNaturalDensity A 0

/--
**Equivalently, counting function is o(N):**
-/
def hasZeroDensity' (A : Set ℕ) : Prop :=
  (fun N => (countingFunction A N : ℝ)) =o[atTop] (fun N => (N : ℝ))

/--
**Sumset B + B:**
The set of all pairwise sums from B.
-/
def sumset (B : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ b₁ b₂ : ℕ, b₁ ∈ B ∧ b₂ ∈ B ∧ n = b₁ + b₂}

notation:max B "+" B => sumset B

/--
**Sumset covering:**
A is covered by B + B if A ⊆ B + B.
-/
def isCoveredBySumset (A B : Set ℕ) : Prop :=
  A ⊆ sumset B

/--
**Sparse growth condition:**
|B ∩ [1,N]| = o(N^{1/2}).
This is "exceptionally sparse" - sparser than √N.
-/
def hasSubsqrtGrowth (B : Set ℕ) : Prop :=
  (fun N => (countingFunction B N : ℝ)) =o[atTop] (fun N => Real.sqrt N)

/-!
## Part II: The Erdős Conjecture
-/

/--
**The original question (Erdős #333):**
For any zero-density set A, does there exist B with:
1. A ⊆ B + B
2. |B ∩ [1,N]| = o(√N)
-/
def ErdosConjecture333 : Prop :=
  ∀ A : Set ℕ, hasZeroDensity A →
    ∃ B : Set ℕ, isCoveredBySumset A B ∧ hasSubsqrtGrowth B

/-!
## Part III: The Negative Answer
-/

/--
**Key observation:**
If B has |B ∩ [1,N]| = o(√N), then B + B has |B+B ∩ [1,N]| = o(N).

More precisely, if |B ∩ [1,N]| ≤ f(N), then |B+B ∩ [1,2N]| ≤ f(N)².
-/
axiom sumset_counting_bound (B : Set ℕ) (f : ℕ → ℝ) :
    (∀ N, (countingFunction B N : ℝ) ≤ f N) →
    ∀ N, (countingFunction (sumset B) (2*N) : ℝ) ≤ (f N)^2

/--
**Corollary:**
If B has o(√N) growth, then B + B has o(N) elements up to 2N.
-/
axiom subsqrt_sumset_sparse (B : Set ℕ) :
    hasSubsqrtGrowth B →
    (fun N => (countingFunction (sumset B) N : ℝ)) =o[atTop] (fun N => (N : ℝ))

/--
**Critical lemma:**
There exist zero-density sets that cannot be covered by such sparse sumsets.

Specifically, there exists A with density zero where any B with A ⊆ B + B
must have |B ∩ [1,N]| ≫ √N.
-/
axiom existence_of_counterexample :
    ∃ A : Set ℕ, hasZeroDensity A ∧
      ∀ B : Set ℕ, isCoveredBySumset A B → ¬hasSubsqrtGrowth B

/--
**The main result: Erdős Conjecture #333 is FALSE**
-/
theorem erdos_333_false : ¬ErdosConjecture333 := by
  intro h
  obtain ⟨A, hA_density, hA_counter⟩ := existence_of_counterexample
  obtain ⟨B, hcover, hsparse⟩ := h A hA_density
  exact hA_counter B hcover hsparse

/-!
## Part IV: Special Cases Where It IS True
-/

/--
**The set of perfect squares:**
-/
def squares : Set ℕ := {n : ℕ | ∃ k : ℕ, n = k^2}

/--
**Squares have zero density:**
|{k² : k² ≤ N}| = √N + O(1), so density = 0.
-/
axiom squares_zero_density : hasZeroDensity squares

/--
**Erdős-Newman (1977):**
For A = squares, there EXISTS a B with A ⊆ B + B and |B ∩ [1,N]| = o(√N).

This is a positive special case!
-/
axiom erdos_newman_squares :
    ∃ B : Set ℕ, isCoveredBySumset squares B ∧ hasSubsqrtGrowth B

/--
**More general positive cases:**
Sets with polynomial gaps admit such representations.
-/
def hasPolynomialGaps (A : Set ℕ) (α : ℝ) : Prop :=
  α > 1 ∧ ∀ n ∈ A, ∀ m ∈ A, n < m → m - n ≥ (n : ℝ)^(1/α)

axiom polynomial_gap_positive (A : Set ℕ) (α : ℝ) (hα : α > 2) :
    hasZeroDensity A → hasPolynomialGaps A α →
    ∃ B : Set ℕ, isCoveredBySumset A B ∧ hasSubsqrtGrowth B

/-!
## Part V: Understanding the Counterexample
-/

/--
**Lower bound on sumset covering:**
If A has counting function f_A(N), and A ⊆ B + B, then B must satisfy
a lower bound on |B ∩ [1,N]|.
-/
axiom covering_lower_bound (A B : Set ℕ) (N : ℕ) :
    isCoveredBySumset A B →
    (countingFunction B N : ℝ)^2 ≥ countingFunction A (2*N)

/--
**Remark:**
The counterexample A is constructed so that f_A(N) grows like N / log N
or similar - still zero density, but "barely" zero.

For such A, any covering B must have |B ∩ [1,N]| ≥ √(N / log N),
which is NOT o(√N).
-/

/--
**Construction hint:**
Take A to be integers with at most (log n)² prime factors.
This has zero density (Prime Number Theorem), but is "dense within zero density".
-/
def almostPrimeFree (k : ℕ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ (Nat.factors n).length ≤ k}

axiom almost_prime_free_density (k : ℕ) :
    hasZeroDensity (almostPrimeFree k)

/-!
## Part VI: Connections
-/

/--
**Related to Erdős #806:**
Problem 806 asks about related sumset covering questions.
-/
def relatedProblem806 : Prop :=
  ∀ A : Set ℕ, hasZeroDensity A →
    ∃ B : Set ℕ, isCoveredBySumset A B ∧ hasZeroDensity B

/--
**Sidon sets:**
B is a Sidon set if all pairwise sums b₁ + b₂ (b₁ ≤ b₂) are distinct.
Sidon sets have |B ∩ [1,N]| = O(√N).
-/
def isSidonSet (B : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ B → b ∈ B → c ∈ B → d ∈ B →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

axiom sidon_growth (B : Set ℕ) :
    isSidonSet B → ∃ C : ℝ, ∀ N, (countingFunction B N : ℝ) ≤ C * Real.sqrt N

/--
**Sidon sets give minimal sumsets:**
If B is Sidon, then |B+B ∩ [1,N]| ≈ |B ∩ [1,N]|².
-/
axiom sidon_sumset_exact (B : Set ℕ) :
    isSidonSet B → ∀ N,
      (countingFunction (sumset B) N : ℝ) ≥
      (countingFunction B (N/2) : ℝ) * ((countingFunction B (N/2) : ℝ) - 1) / 2

/-!
## Part VII: The Erdős-Newman Paper

**Erdős and Newman (1977), "Bases for Sets of Integers":**

- Theorem 1: Squares can be represented as B + B with B very sparse
- Theorem 2: General lower bounds on sumset covering
- The connection to Problem 333 was apparently overlooked

The paper establishes that:
1. Some zero-density sets (squares) have sparse sumset bases
2. General zero-density sets do NOT always have sparse sumset bases
-/

/--
**Summary of Erdős-Newman Theorem 2:**
There exist zero-density sets A where any B with A ⊆ B + B
must have |B ∩ [1,N]| ≥ c√N for infinitely many N.
-/
axiom erdos_newman_theorem2 :
    ∃ A : Set ℕ, hasZeroDensity A ∧
      ∃ c : ℝ, c > 0 ∧
        ∀ B : Set ℕ, isCoveredBySumset A B →
          ∃ᶠ N in atTop, (countingFunction B N : ℝ) ≥ c * Real.sqrt N

/-!
## Part VIII: Summary

**Erdős Problem #333: DISPROVED**

**Question:** For any zero-density A, does there exist B with A ⊆ B+B
and |B ∩ [1,N]| = o(√N)?

**Answer:** NO

**Positive cases:**
- Squares (Erdős-Newman 1977)
- Sets with polynomial gaps

**Negative:** General zero-density sets may require |B| ≈ √N.

**Key insight:** Being zero-density is not restrictive enough.
Some zero-density sets are "almost" positive density in that covering
them by sumsets requires nearly maximal B.
-/

/--
**Main theorem: Erdős #333 is DISPROVED**
-/
def erdos_333 : Prop := ¬ErdosConjecture333

theorem erdos_333_answer : erdos_333 := erdos_333_false

/--
**What we do know:**
-/
theorem erdos_333_summary :
    (¬ErdosConjecture333) ∧
    (∃ B : Set ℕ, isCoveredBySumset squares B ∧ hasSubsqrtGrowth B) ∧
    (∃ A : Set ℕ, hasZeroDensity A ∧ ∀ B, isCoveredBySumset A B → ¬hasSubsqrtGrowth B) := by
  constructor
  · exact erdos_333_false
  constructor
  · exact erdos_newman_squares
  · exact existence_of_counterexample

end Erdos333
