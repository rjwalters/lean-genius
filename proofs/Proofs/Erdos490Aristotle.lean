/-
  Aristotle targets for Erdős Problem #490
  Routine supporting lemmas for automated proof search.
  See Erdos490Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT Szemerédi's main theorem or deep analytic results
  - Known results provable from Mathlib (cardinality bounds, prime divisibility)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos490Aristotle

open Finset

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Subset Cardinality Bounds
-- ═══════════════════════════════════════════════════════════════════

/-- A set A ⊆ {1,...,N}. -/
def IsSubsetUpTo (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- If A ⊆ {1,...,N}, then |A| ≤ N. -/
theorem card_le_of_subset_up_to (A : Finset ℕ) (N : ℕ) (hA : IsSubsetUpTo A N) :
    A.card ≤ N := by
  have hsub : A ⊆ Finset.Icc 1 N := by
    intro a ha; exact Finset.mem_Icc.mpr (hA a ha)
  calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsub
    _ = N := by simp [Nat.card_Icc]

/-- Trivial bound: |A||B| ≤ N² for A, B ⊆ {1,...,N}. -/
theorem trivial_product_bound (A B : Finset ℕ) (N : ℕ)
    (hA : IsSubsetUpTo A N) (hB : IsSubsetUpTo B N) :
    A.card * B.card ≤ N ^ 2 := by
  have hA' := card_le_of_subset_up_to A N hA
  have hB' := card_le_of_subset_up_to B N hB
  calc A.card * B.card ≤ N * N := Nat.mul_le_mul hA' hB'
    _ = N ^ 2 := by ring

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Prime Divisibility for Distinct Products
-- ═══════════════════════════════════════════════════════════════════

/-- If p is prime, 0 < a < p, and p | a * q, then p | q. -/
theorem prime_dvd_of_dvd_mul_lt (p a q : ℕ) (hp : Nat.Prime p)
    (ha : 0 < a) (hpa : a < p) (h : p ∣ a * q) : p ∣ q := by
  have hna : ¬(p ∣ a) := fun hdvd =>
    Nat.not_lt.mpr (Nat.le_of_dvd ha hdvd) hpa
  exact (hp.dvd_mul.mp h).resolve_left hna

/-- If a₁ * p₁ = a₂ * p₂ with p₁, p₂ prime and p₁ > a₂, p₂ > a₁,
    then a₁ = a₂ and p₁ = p₂. -/
theorem unique_product_large_primes (a₁ a₂ p₁ p₂ : ℕ)
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
    (hlt₁ : a₁ < p₁) (hlt₂ : a₂ < p₂)
    (ha₁ : a₁ > 0) (ha₂ : a₂ > 0)
    (heq : a₁ * p₁ = a₂ * p₂) : a₁ = a₂ ∧ p₁ = p₂ := by
  have hp₁_dvd : p₁ ∣ a₂ * p₂ := ⟨a₁, by rw [← heq]; ring⟩
  have hp₂_dvd : p₂ ∣ a₁ * p₁ := ⟨a₂, by rw [heq]; ring⟩
  rcases hp₁.dvd_mul.mp hp₁_dvd with h₁ | h₁
  · -- p₁ | a₂
    rcases hp₂.dvd_mul.mp hp₂_dvd with h₂ | h₂
    · -- p₂ | a₁ and p₁ | a₂: contradiction via size bounds
      have : p₁ ≤ a₂ := Nat.le_of_dvd (by omega) h₁
      have : p₂ ≤ a₁ := Nat.le_of_dvd (by omega) h₂
      omega
    · -- p₂ | p₁: both prime, so p₁ = p₂
      rcases hp₁.eq_one_or_self_of_dvd p₂ h₂ with h | h
      · have := hp₂.two_le; omega
      · have hpp : p₁ = p₂ := h.symm
        subst hpp
        refine ⟨?_, rfl⟩
        have hp₁_pos : 0 < p₁ := hp₁.pos
        exact Nat.eq_of_mul_eq_mul_right hp₁_pos heq
  · -- p₁ | p₂: both prime, so p₁ = p₂
    rcases hp₂.eq_one_or_self_of_dvd p₁ h₁ with h | h
    · have := hp₁.two_le; omega
    · have hpp : p₁ = p₂ := h
      subst hpp
      refine ⟨?_, rfl⟩
      have hp₁_pos : 0 < p₁ := hp₁.pos
      exact Nat.eq_of_mul_eq_mul_right hp₁_pos heq

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Product Set Properties
-- ═══════════════════════════════════════════════════════════════════

/-- The product set A·B = {ab : a ∈ A, b ∈ B}. -/
def productSet (A B : Finset ℕ) : Finset ℕ :=
  A.biUnion (fun a => B.image (fun b => a * b))

/-- |A · B| ≤ |A| · |B| always. -/
theorem productSet_card_le (A B : Finset ℕ) :
    (productSet A B).card ≤ A.card * B.card := by
  unfold productSet
  calc (A.biUnion (fun a => B.image (fun b => a * b))).card
      ≤ A.sum (fun a => (B.image (fun b => a * b)).card) := Finset.card_biUnion_le
    _ ≤ A.sum (fun _ => B.card) :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = A.card * B.card := by simp [Finset.sum_const, Algebra.id.smul_eq_mul]

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Primes are Multiplicative Sidon
-- ═══════════════════════════════════════════════════════════════════

/-- If p₁, p₂, q₁, q₂ are primes with p₁ * q₁ = p₂ * q₂,
    then {p₁, q₁} = {p₂, q₂} as multisets. -/
theorem prime_product_unique (p₁ p₂ q₁ q₂ : ℕ)
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
    (hq₁ : Nat.Prime q₁) (hq₂ : Nat.Prime q₂)
    (h : p₁ * q₁ = p₂ * q₂) :
    (p₁ = p₂ ∧ q₁ = q₂) ∨ (p₁ = q₂ ∧ q₁ = p₂) := by
  have hp₁_dvd : p₁ ∣ p₂ * q₂ := ⟨q₁, by rw [← h]⟩
  rcases hp₁.dvd_mul.mp hp₁_dvd with h₁ | h₁
  · -- p₁ | p₂: both prime, so p₁ = p₂
    rcases hp₂.eq_one_or_self_of_dvd p₁ h₁ with heq | heq
    · have := hp₁.two_le; omega
    · left; refine ⟨heq, ?_⟩
      subst heq
      exact Nat.eq_of_mul_eq_mul_left hp₁.pos h
  · -- p₁ | q₂: both prime, so p₁ = q₂
    rcases hq₂.eq_one_or_self_of_dvd p₁ h₁ with heq | heq
    · have := hp₁.two_le; omega
    · right; refine ⟨heq, ?_⟩
      subst heq
      -- h : p₁ * q₁ = p₂ * p₁, so q₁ = p₂
      have h' : p₁ * q₁ = p₁ * p₂ := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left hp₁.pos h'

end Erdos490Aristotle
