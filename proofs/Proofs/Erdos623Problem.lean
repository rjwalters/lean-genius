/-
  Erdős Problem #623: Independence for Functions on Finite Subsets

  Source: https://erdosproblems.com/623
  Status: OPEN (possibly undecidable)
  Prize: None listed

  Statement:
  Let X be a set of cardinality ℵ_ω and f be a function from the finite subsets
  of X to X such that f(A) ∉ A for all A. Must there exist an infinite Y ⊆ X
  that is independent — that is, for all finite B ⊂ Y we have f(B) ∉ Y?

  Background:
  - Posed by Erdős and Hajnal (1958)
  - Erdős-Hajnal proved: if |X| < ℵ_ω, the answer is NO
  - The threshold ℵ_ω is critical
  - Erdős suggested in 1999 this problem is "perhaps undecidable"

  Key Concepts:
  - ℵ_ω (aleph-omega) is the first singular cardinal
  - A "free" function satisfies f(A) ∉ A for all finite A
  - An "independent" set Y has f(B) ∉ Y for all finite B ⊆ Y

  Tags: set-theory, cardinals, combinatorics, independence
-/

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic

namespace Erdos623

open Cardinal Set

/-! ## Part I: Cardinal Background -/

/-- ℵ_ω (aleph-omega) is the first singular cardinal.
    It's the supremum of ℵ_0, ℵ_1, ℵ_2, ... but not equal to any of them.
    This is the critical cardinality in Problem #623. -/
def aleph_omega : Cardinal := ℵ_ ω

/-- ℵ_ω is a limit cardinal (supremum of smaller alephs). -/
theorem aleph_omega_is_limit : aleph_omega.IsLimit := by
  exact Cardinal.isLimit_aleph ω

/-- ℵ_ω is singular (its cofinality is ω, not itself). -/
theorem aleph_omega_is_singular : ¬aleph_omega.IsRegular := by
  intro h
  have := h.cof_eq
  simp [aleph_omega] at this
  -- The cofinality of ℵ_ω is ω, not ℵ_ω
  sorry

/-- ℵ_n < ℵ_ω for all finite n. -/
theorem aleph_n_lt_omega (n : ℕ) : ℵ_ n < aleph_omega := by
  simp [aleph_omega]
  exact Cardinal.aleph_lt_aleph.mpr (Ordinal.nat_lt_omega0 n)

/-! ## Part II: Free Functions -/

/-- A function f : Finset X → X is "free" if f(A) ∉ A for all finite A.
    This ensures f always produces an element outside the input set. -/
def IsFreeFunction {X : Type*} (f : Finset X → X) : Prop :=
  ∀ A : Finset X, f A ∉ A

/-- Example: the minimum element function (if X is well-ordered) is free
    when restricted to output something not in A. -/
theorem exists_free_function (X : Type*) [Infinite X] [Nonempty X] :
    ∃ f : Finset X → X, IsFreeFunction f := by
  -- We can construct f by choosing any element not in A
  -- This exists because X is infinite and A is finite
  sorry

/-! ## Part III: Independent Sets -/

/-- A set Y ⊆ X is "independent" for f if f(B) ∉ Y for all finite B ⊆ Y.
    The image of f on finite subsets of Y always lands outside Y. -/
def IsIndependent {X : Type*} (f : Finset X → X) (Y : Set X) : Prop :=
  ∀ B : Finset X, ↑B ⊆ Y → f B ∉ Y

/-- The empty set is trivially independent. -/
theorem empty_independent {X : Type*} (f : Finset X → X) :
    IsIndependent f ∅ := by
  intro B hB
  simp

/-- Singletons are independent if f({x}) ≠ x. -/
theorem singleton_independent {X : Type*} (f : Finset X → X) (x : X)
    (hfree : IsFreeFunction f) :
    IsIndependent f {x} ↔ f {x} ≠ x := by
  constructor
  · intro hind
    have := hind {x} (by simp)
    simp at this
    exact this
  · intro hne B hB
    simp at hB ⊢
    sorry

/-! ## Part IV: The Erdős-Hajnal Negative Result -/

/-- **Erdős-Hajnal Theorem (1958)**

    If |X| < ℵ_ω, then there exists a free function f with no infinite
    independent set.

    This shows that the cardinality threshold ℵ_ω is critical.
-/
axiom erdos_hajnal_below_aleph_omega (X : Type*) (hX : #X < aleph_omega) :
    ∃ f : Finset X → X, IsFreeFunction f ∧
      ∀ Y : Set X, Y.Infinite → ¬IsIndependent f Y

/-- Consequence: For any ℵ_n (n < ω), there's a counterexample. -/
theorem counterexample_at_aleph_n (n : ℕ) :
    ∃ (X : Type) (_ : #X = ℵ_ n) (f : Finset X → X),
      IsFreeFunction f ∧ ∀ Y : Set X, Y.Infinite → ¬IsIndependent f Y := by
  sorry

/-! ## Part V: The Main Problem (OPEN) -/

/-- **Erdős Problem #623 (OPEN)**

    Does there exist an infinite independent set for every free function
    on a set of cardinality ℵ_ω?

    Status: OPEN - Erdős suggested it might be undecidable (1999)
-/
def erdos_623_conjecture : Prop :=
  ∀ (X : Type) (hX : #X = aleph_omega) (f : Finset X → X),
    IsFreeFunction f → ∃ Y : Set X, Y.Infinite ∧ IsIndependent f Y

/-- The negative formulation. -/
def erdos_623_negative : Prop :=
  ∃ (X : Type) (_ : #X = aleph_omega) (f : Finset X → X),
    IsFreeFunction f ∧ ∀ Y : Set X, Y.Infinite → ¬IsIndependent f Y

/-- The problem is the disjunction of these two cases. -/
theorem erdos_623_dichotomy :
    erdos_623_conjecture ∨ erdos_623_negative := by
  by_cases h : erdos_623_conjecture
  · left; exact h
  · right
    -- If not all have independent sets, some don't
    sorry

/-! ## Part VI: Potential Undecidability -/

/-- Erdős's 1999 comment suggests this problem might be independent of ZFC.

    Many problems at singular cardinals depend on set-theoretic axioms
    beyond ZFC (like large cardinals or forcing axioms).
-/
def potentially_undecidable : Prop :=
  -- This would mean neither conjecture nor negation is provable in ZFC
  True  -- Placeholder - actual formalization would require metamathematics

/-- The cofinality of ℵ_ω plays a key role. -/
theorem cofinality_aleph_omega : aleph_omega.ord.cof = ω := by
  simp [aleph_omega]
  exact Cardinal.cof_aleph ω

/-! ## Part VII: Related Concepts -/

/-- A "chromatic" interpretation: coloring finite sets. -/
def ChromaticVersion {X : Type*} (f : Finset X → X) : Prop :=
  ∃ Y : Set X, Y.Infinite ∧ ∀ B : Finset X, ↑B ⊆ Y → f B ∉ Y

/-- The problem can be viewed as a Ramsey-type question for singular cardinals. -/
def RamseyInterpretation (κ : Cardinal) : Prop :=
  ∀ f : Finset (ULift.{1} (Fin κ.toNat)) → ULift.{1} (Fin κ.toNat),
    IsFreeFunction f → ∃ Y : Set _, Y.Infinite ∧ IsIndependent f Y

/-! ## Part VIII: Finite Cases -/

/-- For finite X, the problem is trivial (no infinite Y exists). -/
theorem finite_case_trivial {X : Type*} [Finite X] (f : Finset X → X) :
    ¬∃ Y : Set X, Y.Infinite ∧ IsIndependent f Y := by
  intro ⟨Y, hInf, _⟩
  exact Set.not_infinite.mpr (Set.toFinite Y) hInf

/-- For countable X = ℵ_0, the answer is NO (Erdős-Hajnal). -/
theorem countable_case_no (X : Type*) (hX : #X = ℵ₀) :
    ∃ f : Finset X → X, IsFreeFunction f ∧
      ∀ Y : Set X, Y.Infinite → ¬IsIndependent f Y := by
  have hlt : #X < aleph_omega := by
    rw [hX]
    exact aleph_n_lt_omega 0
  exact erdos_hajnal_below_aleph_omega X hlt

/-! ## Part IX: The Gap -/

/-- Summary of known results:

    | Cardinality |X|| Result              | Reference      |
    |-------------|---------------------|----------------|
    | Finite      | Trivial (no ∞ Y)    | —              |
    | ℵ_0         | NO (counterexample) | Erdős-Hajnal   |
    | ℵ_1         | NO (counterexample) | Erdős-Hajnal   |
    | ...         | ...                 | ...            |
    | ℵ_n (n < ω) | NO (counterexample) | Erdős-Hajnal   |
    | ℵ_ω         | OPEN                | Problem #623   |
    | > ℵ_ω       | Unknown             | —              |

    The problem asks precisely about the threshold case ℵ_ω.
-/
theorem known_results_summary :
    (∀ n : ℕ, ∃ (X : Type) (_ : #X = ℵ_ n) (f : Finset X → X),
      IsFreeFunction f ∧ ∀ Y : Set X, Y.Infinite → ¬IsIndependent f Y) := by
  intro n
  exact counterexample_at_aleph_n n

/-! ## Part X: Strengthenings and Variants -/

/-- Strengthening: Must Y be uncountable? -/
def erdos_623_uncountable : Prop :=
  ∀ (X : Type) (hX : #X = aleph_omega) (f : Finset X → X),
    IsFreeFunction f → ∃ Y : Set X, #Y > ℵ₀ ∧ IsIndependent f Y

/-- Weakening: Does at least one free f have an infinite independent set? -/
def erdos_623_weak : Prop :=
  ∀ (X : Type) (_ : #X = aleph_omega),
    ∃ (f : Finset X → X) (Y : Set X),
      IsFreeFunction f ∧ Y.Infinite ∧ IsIndependent f Y

/-- The weak version is easier (just need one example). -/
theorem weak_follows_from_strong (h : erdos_623_conjecture) : erdos_623_weak := by
  intro X hX
  -- Take any free function and apply the conjecture
  sorry

end Erdos623

/-!
## Summary

This file formalizes Erdős Problem #623 on independence for functions
from finite subsets.

**Status**: OPEN (possibly undecidable)

**The Problem**: Let X have cardinality ℵ_ω. Let f: Finset(X) → X be a
"free" function (f(A) ∉ A for all A). Must there exist an infinite
"independent" set Y ⊆ X (f(B) ∉ Y for all finite B ⊆ Y)?

**Key Results**:
- Erdős-Hajnal (1958): For |X| < ℵ_ω, the answer is NO
- The threshold ℵ_ω is exactly where the question becomes non-trivial
- Erdős (1999) suggested the problem might be undecidable in ZFC

**Why ℵ_ω is special**:
- ℵ_ω is the first singular cardinal (cofinality ω)
- Problems at singular cardinals often have independence phenomena
- The structure of ℵ_ω as sup{ℵ_n : n < ω} is key

**What we formalize**:
1. Cardinal background (ℵ_ω, singularity, cofinality)
2. Free functions (f(A) ∉ A)
3. Independent sets (f(B) ∉ Y for B ⊆ Y finite)
4. Erdős-Hajnal negative result for |X| < ℵ_ω
5. The main conjecture for |X| = ℵ_ω
6. Discussion of potential undecidability
7. Variants and strengthenings

**Key axiom**:
- `erdos_hajnal_below_aleph_omega`: The negative result for smaller cardinals
-/
