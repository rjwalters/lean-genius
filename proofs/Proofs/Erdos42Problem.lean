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

/-- A Sidon set in {1,...,N} satisfies |A|(|A|-1) ≤ 2(N-1).
    Proof: the map (a₁,a₂) ↦ a₁-a₂ is injective on off-diagonal ordered pairs
    of A by the Sidon property, and the image lies in {-(N-1),...,N-1}\{0}
    which has 2(N-1) elements. -/
theorem sidon_size_bound (A : Finset ℕ) (N : ℕ) (hn : 1 ≤ N)
    (hs : IsSidonSet A) (hi : InInterval A N) :
  A.card * (A.card - 1) ≤ 2 * (N - 1) := by
  -- The difference map on ordered pairs
  let f : ℕ × ℕ → ℤ := fun p => (↑p.1 : ℤ) - ↑p.2
  -- Step 1: f is injective on A.offDiag (by the Sidon property)
  have h_inj : Set.InjOn f ↑A.offDiag := by
    rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb heq
    simp only [Finset.mem_coe, Finset.mem_offDiag] at ha hb
    dsimp only [f] at heq
    -- From equal differences, derive equal ℕ sums
    have h_sum : a₁ + b₂ = b₁ + a₂ := by
      have : (↑(a₁ + b₂) : ℤ) = ↑(b₁ + a₂) := by push_cast; linarith
      exact_mod_cast this
    -- Apply Sidon: {a₁, b₂} = {b₁, a₂}
    have h_set := hs a₁ ha.1 b₂ hb.2.1 b₁ hb.1 a₂ ha.2.1 h_sum
    -- Extract: a₁ ∈ {b₁, a₂}
    have ha₁_mem : a₁ ∈ ({b₁, a₂} : Finset ℕ) := by
      rw [← h_set]; exact Finset.mem_insert_self a₁ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha₁_mem
    rcases ha₁_mem with h_eq | h_eq
    · -- a₁ = b₁ ⟹ a₂ = b₂ from the sum equation
      exact Prod.ext h_eq (by omega)
    · -- a₁ = a₂: contradicts off-diagonal
      exact absurd h_eq ha.2.2
  -- Step 2: Image of f on A.offDiag ⊆ {-(N-1),...,N-1} \ {0}
  have h_sub : A.offDiag.image f ⊆ (Finset.Icc (1 - (↑N : ℤ)) (↑N - 1)).erase 0 := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨⟨a₁, a₂⟩, hmem, rfl⟩ := hd
    rw [Finset.mem_offDiag] at hmem
    dsimp only [f]
    rw [Finset.mem_erase, Finset.mem_Icc]
    refine ⟨?_, ?_, ?_⟩
    · intro h; apply hmem.2.2
      exact_mod_cast show (↑a₁ : ℤ) = ↑a₂ by linarith
    · have : (1 : ℤ) ≤ ↑a₁ := by exact_mod_cast (hi a₁ hmem.1).1
      have : (↑a₂ : ℤ) ≤ ↑N := by exact_mod_cast (hi a₂ hmem.2.1).2
      linarith
    · have : (↑a₁ : ℤ) ≤ ↑N := by exact_mod_cast (hi a₁ hmem.1).2
      have : (1 : ℤ) ≤ ↑a₂ := by exact_mod_cast (hi a₂ hmem.2.1).1
      linarith
  -- Step 3: Target set has 2*(N-1) elements
  have h_card : ((Finset.Icc (1 - (↑N : ℤ)) (↑N - 1)).erase 0).card = 2 * (N - 1) := by
    rw [Finset.card_erase_of_mem (by rw [Finset.mem_Icc]; constructor <;> omega)]
    rw [Int.card_Icc]
    omega
  -- Step 4: |A|*(|A|-1) = |offDiag|
  have h_offDiag : A.card * (A.card - 1) = A.offDiag.card := by
    rw [Finset.offDiag_card]
    generalize A.card = m
    cases m with
    | zero => simp
    | succ n =>
      simp only [show (n + 1) * (n + 1) = (n + 1) * n + (n + 1) from by ring,
                  Nat.add_sub_cancel]
  -- Combine
  rw [h_offDiag]
  calc A.offDiag.card
      = (A.offDiag.image f).card := (Finset.card_image_of_injOn h_inj).symm
    _ ≤ ((Finset.Icc (1 - (↑N : ℤ)) (↑N - 1)).erase 0).card := Finset.card_le_card h_sub
    _ = 2 * (N - 1) := h_card

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
/-- M = 3 case: also proved by Sedov -/
/- ## The Erdős Problem -/

/-- Erdős Problem 42: For every M ≥ 1 and N sufficiently large,
    every maximal Sidon set A ⊆ {1,...,N} has a companion Sidon set
    B of size M with (A−A) ∩ (B−B) = {0} -/
/-- Constructive version: there exists a function f(M) bounding N₀ -/
