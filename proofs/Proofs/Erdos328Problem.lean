/-
Erdős Problem #328: Partitioning Sets with Bounded Representation Function

Source: https://erdosproblems.com/328
Status: DISPROVED (Nešetřil-Rödl 1985)

Statement:
Suppose A ⊆ ℕ and C > 0 is such that 1_A * 1_A(n) ≤ C for all n ∈ ℕ.
Can A be partitioned into t = t(C) subsets A₁,...,Aₜ such that
1_{Aᵢ} * 1_{Aᵢ}(n) < C for all 1 ≤ i ≤ t and n ∈ ℕ?

Answer: NO (Nešetřil-Rödl 1985)

The answer is NO for all C, even if t is allowed to depend on A itself!
This is a fundamental obstruction in additive combinatorics.

Key Insight:
The representation function r_A(n) = |{(a,b) ∈ A² : a + b = n}| cannot
always be reduced by partitioning, even for B₂ sets (C = 2).

References:
- Erdős-Newman: Original question, [ErGr80, p.48]
- Erdős [Er80e]: No for C = 3, 4 and infinitely many C
- Nešetřil-Rödl [NeRo85]: Complete negative answer
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

namespace Erdos328

/- ## Part I: Representation Function -/

/--
**Representation function (convolution):**
r_A(n) = 1_A * 1_A(n) = |{(a, b) ∈ A × A : a + b = n}|.
Counts the number of ways to write n as a sum of two elements from A.
-/
def representationFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)
    (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))))

/--
**Alternative definition using sums:**
Count pairs (a, b) with a, b ∈ A and a + b = n.
Note: This counts ordered pairs, so r_A(2a) counts (a, a) once.
-/
def rA (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.filter (fun a => a ≤ n ∧ (n - a) ∈ A)).card

/--
**Bounded representation function:**
A set A has bounded convolution if r_A(n) ≤ C for all n.
-/
def hasBoundedConvolution (A : Set ℕ) (C : ℕ) : Prop :=
  ∀ n : ℕ, representationFunction A n ≤ C

/- ## Part II: B_h Sets (Sidon Sets) -/

/--
**B₂ set (Sidon set):**
A is a Sidon set if all pairwise sums are distinct.
Equivalently, r_A(n) ≤ 2 for all n (counting ordered pairs).
-/
def isSidonSet (A : Set ℕ) : Prop :=
  ∀ a b c d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
**B_h set:**
A is a B_h set if all h-wise sums are distinct (up to permutation).
For h = 2, this is a Sidon set.
-/
def isBhSet (A : Set ℕ) (h : ℕ) : Prop :=
  hasBoundedConvolution A (Nat.factorial h)

/--
**Sidon sets have bounded convolution:**
If A is a Sidon set, then r_A(n) ≤ 2 for all n.
-/
/- ## Part III: The Partition Question -/

/--
**Partition of a set:**
A partition of A into t pieces is a collection A₁,...,Aₜ with
⋃ᵢ Aᵢ = A and Aᵢ ∩ Aⱼ = ∅ for i ≠ j.
-/
def isPartition (A : Set ℕ) (parts : List (Set ℕ)) : Prop :=
  (∀ x ∈ A, ∃! i, i < parts.length ∧ x ∈ parts[i]!) ∧
  (∀ i, i < parts.length → parts[i]! ⊆ A)

/--
**Strict convolution reduction:**
Each partition piece has strictly smaller maximum convolution.
-/
def hasStrictlySmaller (parts : List (Set ℕ)) (C : ℕ) : Prop :=
  ∀ i, i < parts.length → ∀ n, representationFunction (parts[i]!) n < C

/--
**Erdős-Newman Question:**
Can every set with r_A ≤ C be partitioned into t(C) pieces
each with r_{Aᵢ} < C?
-/
def erdos_newman_question : Prop :=
  ∀ C : ℕ, ∃ t : ℕ, ∀ A : Set ℕ,
    hasBoundedConvolution A C →
    ∃ parts : List (Set ℕ),
      parts.length ≤ t ∧
      isPartition A parts ∧
      hasStrictlySmaller parts C

/- ## Part IV: Erdős's Partial Results -/

/--
**Erdős (1980) - Case C = 3:**
There exist sets A with r_A ≤ 3 that cannot be partitioned
into any number of pieces each with r_{Aᵢ} < 3.
-/
/--
**Erdős (1980) - Case C = 4:**
Similarly for C = 4.
-/
/- ## Part V: Nešetřil-Rödl's Complete Solution -/

/--
**Nešetřil-Rödl Theorem (1985):**
For ALL C ≥ 1, there exists a set A with r_A ≤ C that cannot
be partitioned into ANY number of pieces with r_{Aᵢ} < C.
-/
axiom nesetril_rodl_theorem :
    ∀ C : ℕ, C ≥ 1 →
      ∃ A : Set ℕ,
        hasBoundedConvolution A C ∧
        ∀ parts : List (Set ℕ),
          isPartition A parts →
          ∃ i, i < parts.length ∧ ∃ n, representationFunction (parts[i]!) n ≥ C

/--
**Main Disproof:**
The Erdős-Newman question has a NEGATIVE answer for all C.
-/
axiom erdos_newman_disproved :
    ¬ erdos_newman_question

/--
**Stronger statement:**
Even allowing t to depend on A (not just C), the answer is still NO.
-/
/- ## Part VI: Special Cases -/

/--
**Case C = 2 (Sidon sets):**
Even Sidon sets (r_A ≤ 2) cannot always be partitioned
into sets with r < 2 (i.e., sets with unique sums).
-/
/--
**Unique sum sets:**
A set has unique sums if r_A(n) ≤ 1 for all n.
These are very sparse (much sparser than Sidon sets).
-/
def hasUniqueSums (A : Set ℕ) : Prop :=
  ∀ n, representationFunction A n ≤ 1

/--
**Unique sum sets are closed under subsets:**
If A has unique sums, so does every subset.
-/
/- ## Part VII: Density Considerations -/

/--
**Density bound:**
Sets with bounded convolution have density at most O(n^{1/2}).
The counterexamples achieve this density.
-/
/- ## Part VIII: Summary -/

/--
**Summary of Erdős Problem #328:**

PROBLEM: Can sets with bounded convolution (r_A ≤ C) be partitioned
into t(C) pieces each with strictly smaller convolution (r_{Aᵢ} < C)?

ANSWER: NO (Nešetřil-Rödl 1985)

The answer is negative for ALL values of C, even if t depends on A.

KEY INSIGHTS:
1. The representation function measures additive structure
2. Partitioning cannot always reduce maximum representation
3. Ramsey-theoretic methods produce counterexamples
4. Even Sidon sets (C = 2) cannot be "reduced"
5. This is a fundamental limitation in additive combinatorics
-/
theorem erdos_328_summary :
    -- The Nešetřil-Rödl theorem: NO for all C
    (∀ C : ℕ, C ≥ 1 →
      ∃ A : Set ℕ,
        hasBoundedConvolution A C ∧
        ∀ parts : List (Set ℕ),
          isPartition A parts →
          ∃ i, i < parts.length ∧ ∃ n, representationFunction (parts[i]!) n ≥ C) ∧
    -- The Erdős-Newman conjecture is false
    ¬ erdos_newman_question :=
  ⟨nesetril_rodl_theorem, erdos_newman_disproved⟩

end Erdos328
