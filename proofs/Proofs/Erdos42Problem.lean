/-
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

import Mathlib

/- ## Sidon Set Definitions -/

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

/- ## Difference Sets -/

/-- The difference set A − A = {a₁ − a₂ : a₁, a₂ ∈ A} (as integers) -/
def diffSet (A : Finset ℕ) : Finset ℤ :=
  Finset.image (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ)) (A ×ˢ A)

/-- Two sets have disjoint difference sets (intersecting only at 0) -/
def DisjointDiffs (A B : Finset ℕ) : Prop :=
  ∀ d : ℤ, d ∈ diffSet A → d ∈ diffSet B → d = 0

/- ## Basic Properties -/

/-- A Sidon set in {1,...,N} has size at most ~√(2N).
    By difference counting: all A.card*(A.card-1) ordered nonzero differences
    are distinct and lie in {-(N-1),...,-1, 1,...,N-1} (2*(N-1) elements).
    Note: the previous bound A.card² ≤ 2N+1 was incorrect
    (counterexample: {1,2,5,7} ⊂ [1,7] has |A|²=16 > 15=2·7+1). -/
axiom sidon_size_bound (A : Finset ℕ) (N : ℕ) (hn : 1 ≤ N)
    (hs : IsSidonSet A) (hi : InInterval A N) :
  A.card * (A.card - 1) ≤ 2 * (N - 1)

/-- 0 is always in A − A: pick any a ∈ A, then a - a = 0. -/
theorem zero_in_diffSet (A : Finset ℕ) (hne : A.Nonempty) :
  (0 : ℤ) ∈ diffSet A := by
  obtain ⟨a, ha⟩ := hne
  simp only [diffSet, Finset.mem_image, Finset.mem_product]
  exact ⟨(a, a), ⟨ha, ha⟩, by simp⟩

/-- {1, 2, 4} is a Sidon set: all pairwise sums are distinct. -/
private theorem sidon_124 : IsSidonSet ({1, 2, 4} : Finset ℕ) := by
  intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ hsum
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha₁ ha₂ hb₁ hb₂
  -- Enumerate all cases
  rcases ha₁ with rfl | rfl | rfl <;> rcases hb₁ with rfl | rfl | rfl <;>
    rcases ha₂ with rfl | rfl | rfl <;> rcases hb₂ with rfl | rfl | rfl <;>
    simp_all (config := { decide := true })

/-- {1, 2, 4} ⊆ {1,...,4} -/
private theorem interval_124 : InInterval ({1, 2, 4} : Finset ℕ) 4 := by
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> omega

/-- {1, 2, 4} is a maximal Sidon set in {1,...,4}: adding 3 breaks Sidon. -/
theorem example_maximal_sidon : IsMaximalSidon ({1, 2, 4} : Finset ℕ) 4 := by
  refine ⟨sidon_124, interval_124, fun x hx1 hx4 hxA => ?_⟩
  -- x ∈ {1,...,4} \ {1,2,4}, so x = 3
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxA
  have : x = 3 := by omega
  subst this
  -- Show {1,2,3,4} is not Sidon: 1+3 = 2+2 = 4 but {1,3} ≠ {2,2}
  intro hSidon
  have h := hSidon 1 (by simp) 3 (by simp) 2 (by simp) 2 (by simp) (by ring)
  -- h : {1, 3} = {2, 2} = {2}. But 1 ∈ {1, 3} and 1 ∉ {2}.
  have : (1 : ℕ) ∈ ({1, 3} : Finset ℕ) := by simp
  rw [h] at this
  simp at this

/- ## Partial Results -/

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

/- ## The Erdős Problem -/

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
