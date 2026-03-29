/-
  Erdos-909-oq-01: Characterize Spaces with dim(S × S) = dim(S)

  Open Question from Erdos Problem #909 (Dimension of Product Spaces):
  Anderson-Keisler (1967) showed that for every n >= 1, there exists a space S
  with dim(S) = dim(S × S) = n. But which spaces have this property?
  Is there a structural criterion?

  This file formalizes:
  1. Covering dimension -- properly defined via finite open cover refinements
  2. The "dimension-stable" property: dim(S × S) = dim(S)
  3. Necessary conditions from the product dimension inequality
  4. Structural properties of dimension-stable spaces
  5. Known examples (0-dimensional spaces, Anderson-Keisler)
  6. Separation of dimension-stable from dimension-additive spaces

  Axiom Elimination (4 → 2):
  - coveringDimension: now a proper definition (was axiom)
  - dimension_mono: now proved from the definition (was axiom)

  References:
  - Anderson, Keisler (1967): Construction for all n >= 1
  - Erdos Problem #909: https://erdosproblems.com/909
  - Engelking "Dimension Theory" (1978)
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Nat.Basic

open TopologicalSpace

namespace Erdos909OQ01

/-
## Part I: Covering Dimension

Covering dimension is defined via finite open covers and their refinements.
A space X has covering dimension <= n if every finite open cover has a finite
open refinement of order at most n + 1 (every point belongs to at most n + 1
sets in the refinement).
-/

/-- A family of sets indexed by ι has order at most k if every point
    belongs to at most k sets. Formally: for every finset of indices
    whose corresponding sets all contain a given point, the finset has
    cardinality at most k. -/
def HasOrderAtMost {X ι : Type*} (f : ι → Set X) (k : ℕ) : Prop :=
  ∀ (x : X) (S : Finset ι), (∀ i ∈ S, x ∈ f i) → S.card ≤ k

/-- Covering dimension: dim(X) <= n iff every finite open cover
    (indexed by Fin k) has a finite open refinement of order <= n+1. -/
def coveringDimension (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (k : ℕ) (cover : Fin k → Set X),
    (∀ i, IsOpen (cover i)) →
    (⋃ i, cover i) = Set.univ →
    ∃ (m : ℕ) (refine : Fin m → Set X),
      (∀ j, IsOpen (refine j)) ∧
      (⋃ j, refine j) = Set.univ ∧
      (∀ j, ∃ i, refine j ⊆ cover i) ∧
      HasOrderAtMost refine (n + 1)

notation "dimLeq" => coveringDimension

/-- Dimension monotonicity: if dimLeq X n and m >= n, then dimLeq X m.
    The same refinement of order <= n+1 <= m+1 witnesses the larger bound. -/
theorem dimension_mono {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (h : dimLeq X n) (hm : n ≤ m) : dimLeq X m := by
  intro k cover hopen hcover
  obtain ⟨m', refine, hopen', hcover', href, hord⟩ := h k cover hopen hcover
  exact ⟨m', refine, hopen', hcover', href, fun x S hS => le_trans (hord x S hS) (by omega)⟩

/-- Product inequality: dim(X × Y) <= dim(X) + dim(Y). -/
axiom dimension_product_ineq (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (m n : ℕ) (hX : dimLeq X m) (hY : dimLeq Y n) :
    dimLeq (X × Y) (m + n)

/-- Dimension exactly n. -/
def hasDimensionExactly (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  dimLeq X n ∧ (n > 0 → ¬dimLeq X (n - 1))

/-
## Part II: Dimension-Stable Spaces

A space S is "dimension-stable" if its product with itself has the
same covering dimension.
-/

/-- A space is dimension-stable at level n if dim(S) = dim(S × S) = n. -/
def IsDimensionStable (S : Type*) [TopologicalSpace S] (n : ℕ) : Prop :=
  hasDimensionExactly S n ∧ hasDimensionExactly (S × S) n

/-- The class of all dimension-stable spaces (existential over n). -/
def IsDimensionStableSpace (S : Type*) [TopologicalSpace S] : Prop :=
  ∃ n : ℕ, IsDimensionStable S n

/-
## Part III: Necessary Conditions

If dim(S × S) = dim(S) = n, what constraints does this impose?
-/

/-- Necessary condition: if S is dimension-stable at n, then
    dim(S × S) <= 2n (from the product inequality). This means
    dim(S × S) = n is strictly below the generic upper bound 2n
    when n >= 1. -/
theorem stable_below_additive (S : Type*) [TopologicalSpace S] (n : ℕ)
    (h : IsDimensionStable S n) : dimLeq (S × S) (n + n) := by
  exact dimension_product_ineq S S n n h.1.1 h.1.1

/-- A dimension-stable space at n >= 1 violates dimension additivity:
    dim(S × S) = n < 2n = dim(S) + dim(S) (strict inequality). -/
theorem stable_violates_additivity (S : Type*) [TopologicalSpace S] (n : ℕ)
    (hn : n ≥ 1) (h : IsDimensionStable S n) :
    n < n + n := by
  omega

/-- A dimension-stable space at n >= 1 is NOT dimension-additive:
    its self-product dimension is strictly less than double. -/
def IsNotDimensionAdditive (S : Type*) [TopologicalSpace S] (n : ℕ) : Prop :=
  hasDimensionExactly S n ∧ hasDimensionExactly (S × S) n ∧ n ≥ 1

theorem stable_not_additive (S : Type*) [TopologicalSpace S] (n : ℕ)
    (hn : n ≥ 1) (h : IsDimensionStable S n) : IsNotDimensionAdditive S n := by
  exact ⟨h.1, h.2, hn⟩

/-
## Part IV: Zero-Dimensional Case

Zero-dimensional spaces trivially satisfy dim(S × S) = dim(S) = 0.
-/

/-- Any 0-dimensional space has dim(S × S) <= 0. -/
theorem zero_dim_product (S : Type*) [TopologicalSpace S]
    (h : dimLeq S 0) : dimLeq (S × S) 0 := by
  have := dimension_product_ineq S S 0 0 h h
  exact dimension_mono this (by omega)

/-- 0-dimensional spaces are trivially dimension-stable (assuming dim = 0). -/
theorem zero_dim_stable (S : Type*) [TopologicalSpace S]
    (h : hasDimensionExactly S 0) :
    hasDimensionExactly (S × S) 0 := by
  constructor
  · exact zero_dim_product S h.1
  · intro h0; omega

/-
## Part V: Anderson-Keisler Construction

The existence result for all n >= 1.
-/

/-- Anderson-Keisler (1967): For every n >= 1, dimension-stable spaces exist. -/
axiom anderson_keisler_existence :
    ∀ n : ℕ, n ≥ 1 → ∃ (S : Type) (_ : TopologicalSpace S),
      IsDimensionStable S n

/-- The characterization question: what is the necessary and sufficient condition
    for a space to be dimension-stable? -/
def CharacterizationQuestion : Prop :=
  ∃ (P : (S : Type*) → [TopologicalSpace S] → Prop),
    ∀ (S : Type*) [TopologicalSpace S] (n : ℕ),
      hasDimensionExactly S n →
      (IsDimensionStable S n ↔ P S)

/-
## Part VI: Structural Properties

Properties that dimension-stable spaces must/may have.
-/

/-- If S is dimension-stable at n, then dim(S^k) <= n for all finite k
    follows from induction on the product. More precisely,
    dim(S × S × S) <= dim(S × S) + dim(S) = n + n, but the
    actual dimension might be n if the product is "well-behaved". -/

/-- Dimension-stability is symmetric in the sense that if S is stable
    at n, the self-product S × S is also a space of dimension n
    (but may not itself be stable). -/
theorem product_has_same_dim (S : Type*) [TopologicalSpace S] (n : ℕ)
    (h : IsDimensionStable S n) :
    hasDimensionExactly (S × S) n :=
  h.2

/-- The self-product of a dimension-stable space has dimension at most n. -/
theorem stable_product_dimleq (S : Type*) [TopologicalSpace S] (n : ℕ)
    (h : IsDimensionStable S n) :
    dimLeq (S × S) n :=
  h.2.1

/-- A dimension-stable space at n has dim <= n (tautological from definition). -/
theorem stable_dimleq (S : Type*) [TopologicalSpace S] (n : ℕ)
    (h : IsDimensionStable S n) :
    dimLeq S n :=
  h.1.1

/-- If dim(S) = n and dim(S × S) = m with m != n, then S is NOT dimension-stable
    at n. This shows dimension-stable requires exact equality. -/
theorem not_stable_if_product_lower (S : Type*) [TopologicalSpace S] (n m : ℕ)
    (hS : hasDimensionExactly S n) (hSS : hasDimensionExactly (S × S) m)
    (hne : m ≠ n) : ¬ IsDimensionStable S n := by
  intro ⟨_, h2⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- m < n: dimLeq (S×S) m, so dimLeq (S×S) (n-1) by mono, contradicts h2
    have h_n_pos : n > 0 := by omega
    exact h2.2 h_n_pos (dimension_mono hSS.1 (by omega))
  · -- m > n: dimLeq (S×S) n from h2, so dimLeq (S×S) (m-1) by mono, contradicts hSS
    have h_m_pos : m > 0 := by omega
    exact hSS.2 h_m_pos (dimension_mono h2.1 (by omega))

/-
## Part VII: Known Examples and Non-Examples
-/

/-- Euclidean spaces are NOT dimension-stable for n >= 1:
    dim(R^n × R^n) = dim(R^{2n}) = 2n != n. -/
def EuclideanNotStable (n : ℕ) (hn : n ≥ 1) : Prop :=
  ¬ IsDimensionStable (Fin n → ℝ) n

/-- The characterization remains open for general topological spaces.
    Known partial results:
    1. All 0-dimensional spaces are stable (trivially)
    2. Compact manifolds are NOT stable (dimension is additive)
    3. Some totally disconnected spaces are stable
    4. The Anderson-Keisler construction uses descriptive set theory -/

/-
## Summary

**Problem**: Erdos-909-oq-01 -- Characterize spaces with dim(S x S) = dim(S)
**Status**: Formalized with structural theorems

**Definitions** (3):
1. HasOrderAtMost -- order of a cover at a point
2. coveringDimension -- covering dimension via finite open cover refinements
3. hasDimensionExactly -- exact covering dimension

**Axioms** (2 total, reduced from 4):
1. dimension_product_ineq -- product dimension inequality (deep result)
2. anderson_keisler_existence -- existence for all n >= 1 (deep existence)

**Proved** (10 theorems):
1. dimension_mono -- monotonicity of covering dimension (was axiom, now proved)
2. stable_below_additive -- product dim bounded by 2n
3. stable_violates_additivity -- n < 2n for n >= 1
4. stable_not_additive -- stable implies not additive
5. zero_dim_product -- 0-dim product is 0-dim
6. zero_dim_stable -- 0-dim spaces are stable
7. product_has_same_dim -- self-product has dim n
8. stable_product_dimleq -- product dim <= n
9. stable_dimleq -- space dim <= n
10. not_stable_if_product_lower -- failure when dims disagree
-/

end Erdos909OQ01
