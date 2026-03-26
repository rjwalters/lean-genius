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
    Proof: map ordered distinct pairs (a,b) to a+N-b ∈ {1,...,2N-1}\{N}.
    Injective by Sidon, target has 2(N-1) elements. -/
theorem sidon_size_bound (A : Finset ℕ) (N : ℕ) (hn : 1 ≤ N)
    (hs : IsSidonSet A) (hi : InInterval A N) :
    A.card * (A.card - 1) ≤ 2 * (N - 1) := by
  rw [← Finset.card_offDiag]
  -- Map (a, b) with a ≠ b to a + N - b ∈ {1,...,2N-1} \ {N}
  set f : ℕ × ℕ → ℕ := fun p => p.1 + N - p.2 with hf_def
  set T := (Finset.Icc 1 (2 * N - 1)).erase N with hT_def
  -- f maps A.offDiag into T
  have h_maps : ∀ p ∈ A.offDiag, f p ∈ T := by
    intro ⟨a, b⟩ hab
    simp only [Finset.mem_offDiag] at hab
    obtain ⟨ha, hb, hne⟩ := hab
    obtain ⟨ha1, haN⟩ := hi a ha
    obtain ⟨hb1, hbN⟩ := hi b hb
    simp only [hT_def, hf_def, Finset.mem_erase, Finset.mem_Icc]
    exact ⟨by omega, by omega, by omega⟩
  -- f is injective on A.offDiag (key: uses Sidon property)
  have h_inj : Set.InjOn f ↑A.offDiag := by
    intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
    simp only [Finset.mem_coe, Finset.mem_offDiag] at h1 h2
    obtain ⟨ha1, hb1, hne1⟩ := h1
    obtain ⟨ha2, hb2, hne2⟩ := h2
    simp only [hf_def] at heq
    -- a₁+N-b₁ = a₂+N-b₂ implies a₁+b₂ = a₂+b₁
    have hsum : a₁ + b₂ = a₂ + b₁ := by
      have := (hi a₁ ha1).1; have := (hi b₁ hb1).2
      have := (hi a₂ ha2).1; have := (hi b₂ hb2).2
      omega
    -- By Sidon: {a₁, b₂} = {a₂, b₁}
    have hsidon := hs a₁ ha1 b₂ hb2 a₂ ha2 b₁ hb1 hsum
    -- a₁ ∈ {a₂, b₁}
    have ha₁_mem : a₁ ∈ ({a₂, b₁} : Finset ℕ) := hsidon ▸ Finset.mem_insert_self a₁ {b₂}
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha₁_mem
    rcases ha₁_mem with rfl | rfl
    · -- a₁ = a₂, so b₁ = b₂
      exact Prod.ext rfl (by omega)
    · -- a₁ = b₁, contradicts hne1
      exact absurd rfl hne1
  -- T has at most 2*(N-1) elements
  have h_card : T.card ≤ 2 * (N - 1) := by
    simp only [hT_def]
    have hN_mem : N ∈ Finset.Icc 1 (2 * N - 1) := Finset.mem_Icc.mpr ⟨hn, by omega⟩
    rw [Finset.card_erase_of_mem hN_mem]
    simp only [Finset.card_Icc]
    omega
  -- Combine
  calc A.offDiag.card
      = (A.offDiag.image f).card := (Finset.card_image_of_injOn h_inj).symm
    _ ≤ T.card := Finset.card_le_card (Finset.image_subset_iff.mpr h_maps)
    _ ≤ 2 * (N - 1) := h_card

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
