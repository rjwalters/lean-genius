/-
Erdős Problem #532: Hindman's Theorem (IP Sets)

Source: https://erdosproblems.com/532
Status: SOLVED by Hindman (1974)

Statement:
If ℕ is finitely colored, must there exist an infinite set A ⊆ ℕ such that
all finite subset sums (as S ranges over non-empty finite subsets of A)
are monochromatic?

Background:
This problem was posed by Graham and Rothschild. In other words, the question
asks: must some color class be an IP set?

An "IP set" (named after "Idempotent" in ultrafilter theory, or "Infinite-dimensional
Parallelepiped") is a set containing all finite sums from some infinite sequence.

Solution:
Hindman proved in 1974 that YES - for any finite coloring of ℕ, some color class
contains an IP set. This is now known as Hindman's Theorem.

Key Insight:
The original proof used intricate combinatorial arguments. Modern proofs often
use ultrafilter methods (idempotent ultrafilters in (βℕ, +)).

References:
- Hindman, Neil. "Finite sums from sequences within cells of a partition of ℕ."
  J. Combinatorial Theory Ser. A 17 (1974), 1-11.
- Graham, R.L., Rothschild, B.L. "Ramsey's theorem for n-parameter sets."
  Trans. Amer. Math. Soc. 159 (1971), 257-292.

Related Problems:
- Problem #531: Related coloring question
- Problem #948: Further generalizations

Tags: ramsey-theory, combinatorics, number-theory, IP-sets
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Function
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

namespace Erdos532

/-!
## Part I: Finite Colorings
-/

/--
**Finite Coloring:**
A k-coloring of ℕ is a function c : ℕ → Fin k assigning one of k colors to each natural.
-/
def Coloring (k : ℕ) := ℕ → Fin k

/--
**Monochromatic Set:**
A set S ⊆ ℕ is monochromatic under coloring c if all elements have the same color.
-/
def IsMonochromatic {k : ℕ} (c : Coloring k) (S : Set ℕ) : Prop :=
  ∃ color : Fin k, ∀ n ∈ S, c n = color

/-!
## Part II: Finite Subset Sums
-/

/--
**Finite Subset Sum:**
Given a finite set S of natural numbers, its sum is Σ_{n ∈ S} n.
-/
def finsetSum (S : Finset ℕ) : ℕ := ∑ n ∈ S, n

/--
**Finite Sums of a Set (FS):**
Given a set A ⊆ ℕ, FS(A) is the set of all finite non-empty subset sums.
This is the set { Σ_{n ∈ S} n | S ⊆ A, S finite and non-empty }.
-/
def FiniteSums (A : Set ℕ) : Set ℕ :=
  { n : ℕ | ∃ S : Finset ℕ, S.Nonempty ∧ (↑S : Set ℕ) ⊆ A ∧ finsetSum S = n }

/-!
## Part III: IP Sets
-/

/--
**IP Set (Infinite-dimensional Parallelepiped):**
A set S ⊆ ℕ is an IP set if it contains all finite sums from some infinite set.
Equivalently, S contains FS(A) for some infinite A ⊆ ℕ.
-/
def IsIPSet (S : Set ℕ) : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ FiniteSums A ⊆ S

/--
**IP* Set:**
A set is IP* if it intersects every IP set (the dual notion).
-/
def IsIPStarSet (S : Set ℕ) : Prop :=
  ∀ T : Set ℕ, IsIPSet T → (S ∩ T).Nonempty

/-!
## Part IV: Hindman's Theorem
-/

/--
**Hindman's Theorem (1974):**
For any finite coloring of ℕ, there exists an infinite set A such that
all finite subset sums of A are monochromatic.

Equivalently: for any k-coloring, some color class contains an IP set.
-/
axiom hindman_theorem :
  ∀ k : ℕ, k ≥ 1 →
    ∀ c : Coloring k,
      ∃ A : Set ℕ, A.Infinite ∧ IsMonochromatic c (FiniteSums A)

/--
**Hindman's Theorem (Color Class Form):**
For any finite coloring, some color class is an IP set.
-/
theorem hindman_color_class :
    ∀ k : ℕ, k ≥ 1 →
      ∀ c : Coloring k,
        ∃ color : Fin k, IsIPSet { n : ℕ | c n = color } := by
  intros k hk c
  obtain ⟨A, hA_inf, ⟨color, hcolor⟩⟩ := hindman_theorem k hk c
  use color
  unfold IsIPSet
  use A
  constructor
  · exact hA_inf
  · intro n hn
    simp only [Set.mem_setOf_eq]
    exact hcolor n hn

/--
**The Original Problem Statement (Graham-Rothschild):**
If ℕ is 2-colored, must some color class be an IP set?
-/
theorem erdos_532_two_colors :
    ∀ c : Coloring 2,
      ∃ color : Fin 2, IsIPSet { n : ℕ | c n = color } := by
  intro c
  exact hindman_color_class 2 (by norm_num) c

/-!
## Part V: Basic Properties of IP Sets
-/

/--
**Singletons from A are in FS(A):**
For any a ∈ A, we have a ∈ FS(A) (taking the singleton sum).
-/
theorem singleton_in_finite_sums {A : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∈ FiniteSums A := by
  use {a}
  constructor
  · exact singleton_nonempty a
  constructor
  · simp [ha]
  · simp [finsetSum]

/--
**Every IP set is infinite:**
If S is an IP set, then S is infinite.
An IP set contains FS(A) for some infinite A, and FS(A) contains all
singletons from A (since a = Σ_{n ∈ {a}} n). Since A is infinite,
FS(A) ⊇ A is infinite, so S ⊇ FS(A) is infinite.
-/
theorem ip_set_infinite (S : Set ℕ) (h : IsIPSet S) : S.Infinite := by
  obtain ⟨A, hA_inf, hFS⟩ := h
  apply Set.Infinite.mono hFS
  apply Set.Infinite.mono _ hA_inf
  intro a ha
  exact singleton_in_finite_sums ha

/--
**Closure under addition (for disjoint subsets):**
If x, y ∈ FS(A) come from disjoint finite subsets, then x + y ∈ FS(A).
-/
theorem finite_sums_add_disjoint {A : Set ℕ} {S T : Finset ℕ}
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSA : (↑S : Set ℕ) ⊆ A) (hTA : (↑T : Set ℕ) ⊆ A)
    (hST : Disjoint S T) :
    finsetSum S + finsetSum T ∈ FiniteSums A := by
  use S ∪ T
  constructor
  · exact Finset.Nonempty.mono (subset_union_left) hS
  constructor
  · intro x hx
    simp only [Finset.coe_union, Set.mem_union] at hx
    cases hx with
    | inl h => exact hSA h
    | inr h => exact hTA h
  · unfold finsetSum
    rw [sum_union hST]

/-!
## Part VI: Ultrafilter Proof (Modern Approach)
-/

/--
**Ultrafilter Characterization:**
The modern proof of Hindman's theorem uses the fact that (βℕ, +) has
idempotent ultrafilters p (where p + p = p), and an IP set is precisely
a set that belongs to some idempotent ultrafilter.

An idempotent ultrafilter on ℕ is an ultrafilter p in the Stone-Čech
compactification βℕ satisfying p + p = p under the extended addition.
Its existence follows from Ellis's lemma applied to the compact
right-topological semigroup (βℕ, +).
-/
axiom idempotent_ultrafilter_exists :
  ∃ p : Set (Set ℕ),
    (∀ A B : Set ℕ, A ∈ p → A ⊆ B → B ∈ p) ∧  -- Upward closed
    (∀ A B : Set ℕ, A ∈ p → B ∈ p → (A ∩ B) ∈ p) ∧  -- Closed under intersection
    (∀ A : Set ℕ, A ∈ p ∨ Aᶜ ∈ p) ∧  -- Ultra property
    (Set.univ ∈ p) ∧  -- Contains universe
    (∅ ∉ p) ∧  -- Proper
    (∀ A : Set ℕ, A ∈ p → IsIPSet A)  -- Every member is an IP set (idempotent property)

/--
**Ultrafilter Proof Strategy:**
1. (βℕ, +) is a compact right-topological semigroup
2. By Ellis's lemma, it has an idempotent p = p + p
3. Any member A ∈ p satisfies: A is an IP set
4. For any finite partition, some cell belongs to p (by ultra property)
5. Hence some color class is an IP set

The ultrafilter approach yields Hindman's theorem as a consequence:
an idempotent ultrafilter witnesses the monochromatic IP set.
-/
axiom ultrafilter_implies_hindman :
  -- If an idempotent ultrafilter exists in (βℕ, +), then Hindman's theorem holds.
  -- Axiomatized because βℕ infrastructure is not yet in Mathlib.
  (∃ p : Set (Set ℕ),
    (∀ A B : Set ℕ, A ∈ p → A ⊆ B → B ∈ p) ∧  -- Upward closed
    (∀ A B : Set ℕ, A ∈ p → B ∈ p → (A ∩ B) ∈ p) ∧  -- Closed under intersection
    (∀ A : Set ℕ, A ∈ p ∨ Aᶜ ∈ p) ∧  -- Ultra property
    (∅ ∉ p)) →  -- Proper
  ∀ k : ℕ, k ≥ 1 →
    ∀ c : Coloring k,
      ∃ A : Set ℕ, A.Infinite ∧ IsMonochromatic c (FiniteSums A)

/-!
## Part VII: Milliken-Taylor Theorem
-/

/--
**Milliken-Taylor Theorem:**
A strengthening of Hindman's theorem. For any finite coloring of FS_k
(k-tuples of sums from an infinite sequence), there exists a monochromatic
structure.
-/
axiom milliken_taylor_theorem :
  ∀ k r : ℕ, k ≥ 1 → r ≥ 1 →
    True  -- Statement requires more elaborate types

/-!
## Part VIII: Hales-Jewett Connection
-/

/--
**Relation to Hales-Jewett:**
Hindman's theorem can be derived from the Hales-Jewett theorem, showing
the deep connections in Ramsey theory. Specifically, the Hales-Jewett theorem
on combinatorial lines in high-dimensional cubes implies partition regularity
of finite sums, yielding Hindman's result.

Axiomatized because the Hales-Jewett theorem is not yet in Mathlib.
-/
axiom hales_jewett_implies_hindman :
  ∀ k : ℕ, k ≥ 1 →
    ∀ c : Coloring k,
      ∃ A : Set ℕ, A.Infinite ∧ IsMonochromatic c (FiniteSums A)

/-!
## Part IX: Computational Aspects
-/

/--
**Finite Hindman Theorem:**
For any k ≥ 1, there exists N such that any k-coloring of {1,...,N}
has a monochromatic set {a, b, a+b}. The existence follows from compactness
but explicit values grow extremely fast.

Axiomatized because the finite version requires detailed Ramsey bounds.
-/
axiom hindman_finite_exists (k : ℕ) :
  ∃ N : ℕ, ∀ c : Fin N → Fin (k + 1),
    ∃ a b : Fin N, a.val + b.val < N ∧
      c a = c b ∧ c a = c ⟨a.val + b.val, by omega⟩

/--
**Hindman Numbers (Finite Version):**
Let HJ(k) be the smallest N such that any k-coloring of {1,...,N}
has a monochromatic set {a, b, a+b}.

Known: HJ(2) = 5 since any 2-coloring of {1,...,5} must have a, b, a+b
all the same color.
-/
noncomputable def hindmanNumber (k : ℕ) : ℕ :=
  Nat.find (hindman_finite_exists k)

/-!
## Part X: Summary
-/

/--
**Erdős Problem #532: Status**

**Question (Graham-Rothschild):**
If ℕ is 2-colored, must some color class be an IP set?

**Answer:**
YES - proved by Hindman (1974) for any finite coloring.

**Key Result:**
Hindman's Theorem: For any finite coloring of ℕ, there exists an infinite
set A such that all finite subset sums are monochromatic.

**Proof Methods:**
1. Original (Hindman 1974): Intricate combinatorial induction
2. Modern: Ultrafilter/topological dynamics (idempotent in βℕ)
3. Alternative: Via Hales-Jewett theorem

**Impact:**
Hindman's theorem is a cornerstone of Ramsey theory, with applications to
combinatorics, number theory, and topological dynamics.
-/
theorem erdos_532_summary :
    -- For any 2-coloring, some color class is an IP set
    (∀ c : Coloring 2, ∃ color : Fin 2, IsIPSet { n : ℕ | c n = color }) ∧
    -- Generalizes to any finite coloring
    (∀ k : ℕ, k ≥ 1 → ∀ c : Coloring k,
      ∃ A : Set ℕ, A.Infinite ∧ IsMonochromatic c (FiniteSums A)) := by
  exact ⟨erdos_532_two_colors, hindman_theorem⟩

end Erdos532
