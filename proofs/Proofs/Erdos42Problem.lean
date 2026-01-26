/-!
# Erdős Problem #42 — Sidon Sets with Disjoint Difference Sets

A Sidon set (B₂ set) is a set A where all pairwise sums a + b (a ≤ b)
are distinct, equivalently all pairwise differences are distinct.

Erdős asked: For every M ≥ 1 and N sufficiently large, is it true that
for every maximal Sidon set A ⊆ {1,...,N}, there exists another Sidon
set B ⊆ {1,...,N} of size M such that (A−A) ∩ (B−B) = {0}?

Known partial results:
- M = 1: trivial
- M = 2: proved by Sedov
- M = 3: proved by Sedov (computational)

Reference: https://erdosproblems.com/42
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! ## Sidon Set Definitions -/

/-- A finite set is Sidon (B₂) if all pairwise sums are distinct,
    equivalently all nonzero differences are distinct -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ A, ∀ a₂ ∈ A, ∀ b₂ ∈ A,
    a₁ + b₁ = a₂ + b₂ → ({a₁, b₁} : Finset ℕ) = {a₂, b₂}

/-- A ⊆ {1,...,N} -/
def InInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- A is a maximal Sidon set in {1,...,N}: it is Sidon, contained in {1,...,N},
    and no element of {1,...,N} \ A can be added while preserving Sidon -/
def IsMaximalSidon (A : Finset ℕ) (N : ℕ) : Prop :=
  IsSidonSet A ∧ InInterval A N ∧
  ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ A → ¬IsSidonSet (A ∪ {x})

/-! ## Difference Sets -/

/-- The difference set A − A = {a₁ − a₂ : a₁, a₂ ∈ A} (as integers) -/
def diffSet (A : Finset ℕ) : Finset ℤ :=
  A.biUnion (fun a₁ => A.image (fun a₂ => (a₁ : ℤ) - (a₂ : ℤ)))

/-- Two sets have disjoint difference sets (intersecting only at 0) -/
def DisjointDiffs (A B : Finset ℕ) : Prop :=
  ∀ d : ℤ, d ∈ diffSet A → d ∈ diffSet B → d = 0

/-! ## Basic Properties -/

/-- A Sidon set in {1,...,N} has size at most ~√N -/
axiom sidon_size_bound (A : Finset ℕ) (N : ℕ) (hn : 1 ≤ N)
    (hs : IsSidonSet A) (hi : InInterval A N) :
  A.card * A.card ≤ 2 * N + 1

/-- 0 is always in A − A -/
axiom zero_in_diffSet (A : Finset ℕ) (hne : A.Nonempty) :
  (0 : ℤ) ∈ diffSet A

/-- {1, 2, 4} is a maximal Sidon set in {1,...,4} -/
axiom example_maximal_sidon : IsMaximalSidon {1, 2, 4} 4

/-! ## Partial Results -/

/-- M = 2 case: Sedov proved that for large N, every maximal Sidon set
    has a 2-element Sidon set with disjoint differences -/
axiom sedov_M2 :
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, IsMaximalSidon A N →
      ∃ B : Finset ℕ, IsSidonSet B ∧ InInterval B N ∧
        B.card = 2 ∧ DisjointDiffs A B

/-- M = 3 case: also proved by Sedov -/
axiom sedov_M3 :
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, IsMaximalSidon A N →
      ∃ B : Finset ℕ, IsSidonSet B ∧ InInterval B N ∧
        B.card = 3 ∧ DisjointDiffs A B

/-! ## The Erdős Problem -/

/-- Erdős Problem 42: For every M ≥ 1 and N sufficiently large,
    every maximal Sidon set A ⊆ {1,...,N} has a companion Sidon set
    B of size M with (A−A) ∩ (B−B) = {0} -/
axiom ErdosProblem42 :
  ∀ M : ℕ, 1 ≤ M →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℕ, IsMaximalSidon A N →
        ∃ B : Finset ℕ, IsSidonSet B ∧ InInterval B N ∧
          B.card = M ∧ DisjointDiffs A B

/-- Constructive version: there exists a function f(M) bounding N₀ -/
axiom ErdosProblem42_constructive :
  ∃ f : ℕ → ℕ, ∀ M N : ℕ, 1 ≤ M → f M ≤ N →
    ∀ A : Finset ℕ, IsMaximalSidon A N →
      ∃ B : Finset ℕ, IsSidonSet B ∧ InInterval B N ∧
        B.card = M ∧ DisjointDiffs A B
