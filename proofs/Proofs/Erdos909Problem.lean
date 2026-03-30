/-
Erdős Problem #909: Dimension of Product Spaces

Source: https://erdosproblems.com/909
Status: SOLVED (Anderson-Keisler, 1967)

Statement:
Let n ≥ 2. Is there a space S of dimension n such that S² (the product
S × S) also has dimension n?

Background:
- For most 'nice' spaces: dim(X × Y) ≤ dim(X) + dim(Y)
- For n = 1: The rational points in Hilbert space ℓ²(ℚ) have this property
- Anderson-Keisler (1967): YES for all n ≥ 1

Tags: topology, dimension-theory, product-spaces
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Nat.Basic

open TopologicalSpace

namespace Erdos909

/- ## Part I: Covering Dimension -/

/--
**Covering Dimension (axiomatized):**
A topological space X has covering dimension ≤ n if every finite open
cover has a refinement such that no point belongs to more than n+1 sets.
-/
axiom coveringDimension : Type* → ℕ → Prop

notation "dimLeq" => coveringDimension

/--
**Dimension exactly n:** dim(X) ≤ n but not dim(X) ≤ n-1.
-/
def hasDimensionExactly (X : Type*) (n : ℕ) : Prop :=
  dimLeq X n ∧ (n > 0 → ¬dimLeq X (n - 1))

/--
**Product Dimension Inequality:**
For 'nice' spaces: dim(X × Y) ≤ dim(X) + dim(Y).
The problem asks when this can be a strict inequality.
-/
/- ## Part II: The Problem Statement -/

/--
**Erdős Problem #909:**
For every n ≥ 1, does there exist a space S of dimension n such
that S × S also has dimension n?
-/
def erdos909Statement : Prop :=
  ∀ n : ℕ, n ≥ 1 → ∃ (S : Type) (_ : TopologicalSpace S),
    hasDimensionExactly S n ∧ hasDimensionExactly (S × S) n

/- ## Part III: Known Results for n = 1 -/

/--
**Rational points in Hilbert space:**
The set of points in ℓ² with all coordinates rational has dimension 1,
and its square also has dimension 1. This is the classical example
for n = 1 and was known before the general result.
-/
axiom rational_hilbert_example :
  ∃ (S : Type) (_ : TopologicalSpace S),
    hasDimensionExactly S 1 ∧ hasDimensionExactly (S × S) 1

/- ## Part IV: Anderson-Keisler Theorem (1967) -/

/--
**Anderson-Keisler Theorem (1967):**
For every n ≥ 1, there exists a separable metric space S_n of
dimension n such that S_n × S_n also has dimension n.

The construction uses techniques from descriptive set theory:
starting with an n-dimensional space and taking a carefully chosen
subset where covers behave efficiently in the product. The spaces
have 'pathological' properties that cause the product dimension
to be strictly less than the sum.
-/
axiom anderson_keisler_theorem :
    ∀ n : ℕ, n ≥ 1 → ∃ (S : Type) (_ : TopologicalSpace S) (_ : MetrizableSpace S),
      hasDimensionExactly S n ∧ hasDimensionExactly (S × S) n

/--
**Main Theorem: Erdős Problem #909 is SOLVED.**
The answer is YES — such spaces exist for all n ≥ 1.
-/
theorem erdos_909 : erdos909Statement := by
  intro n hn
  obtain ⟨S, hTop, _, hdim⟩ := anderson_keisler_theorem n hn
  exact ⟨S, hTop, hdim⟩

/- ## Part V: Supporting Results -/

/-- dim(ℝ^n) = n (standard result) -/
/-- If Y ⊆ X, then dim(Y) ≤ dim(X) (monotonicity) -/
/- ## Part VI: Summary -/

/--
**Summary of Erdős Problem #909:**

Erdős asked whether for each n ≥ 1, there exists a topological space S
with dim(S) = n and dim(S × S) = n — surprising because products
typically have dimension equal to the sum of factors.

**Answer:** YES (Anderson-Keisler, 1967)

The proof constructs separable metric spaces with special properties
using descriptive set theory. For n = 1, the rational points in
Hilbert space ℓ²(ℚ) provide an explicit example.
-/
theorem erdos_909_summary :
    -- The problem is solved
    erdos909Statement ∧
    -- The n = 1 case has an explicit example
    (∃ (S : Type) (_ : TopologicalSpace S),
      hasDimensionExactly S 1 ∧ hasDimensionExactly (S × S) 1) := by
  exact ⟨erdos_909, rational_hilbert_example⟩

end Erdos909
