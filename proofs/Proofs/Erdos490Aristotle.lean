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
    A.card ≤ N := by sorry

/-- Trivial bound: |A||B| ≤ N² for A, B ⊆ {1,...,N}. -/
theorem trivial_product_bound (A B : Finset ℕ) (N : ℕ)
    (hA : IsSubsetUpTo A N) (hB : IsSubsetUpTo B N) :
    A.card * B.card ≤ N ^ 2 := by sorry

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Prime Divisibility for Distinct Products
-- ═══════════════════════════════════════════════════════════════════

/-- If p is prime, p > a, and p | a * q, then p | q. -/
theorem prime_dvd_of_dvd_mul_lt (p a q : ℕ) (hp : Nat.Prime p)
    (hpa : a < p) (h : p ∣ a * q) : p | q := by sorry

/-- If a₁ * p₁ = a₂ * p₂ with p₁, p₂ prime and p₁ > a₂, p₂ > a₁,
    then a₁ = a₂ and p₁ = p₂. -/
theorem unique_product_large_primes (a₁ a₂ p₁ p₂ : ℕ)
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
    (hlt₁ : a₁ < p₁) (hlt₂ : a₂ < p₂)
    (ha₁ : a₁ > 0) (ha₂ : a₂ > 0)
    (heq : a₁ * p₁ = a₂ * p₂) : a₁ = a₂ ∧ p₁ = p₂ := by sorry

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Product Set Properties
-- ═══════════════════════════════════════════════════════════════════

/-- The product set A·B = {ab : a ∈ A, b ∈ B}. -/
def productSet (A B : Finset ℕ) : Finset ℕ :=
  A.biUnion (fun a => B.image (fun b => a * b))

/-- |A · B| ≤ |A| · |B| always. -/
theorem productSet_card_le (A B : Finset ℕ) :
    (productSet A B).card ≤ A.card * B.card := by sorry

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Primes are Multiplicative Sidon
-- ═══════════════════════════════════════════════════════════════════

/-- If p₁, p₂, q₁, q₂ are primes with p₁ * q₁ = p₂ * q₂,
    then {p₁, q₁} = {p₂, q₂} as multisets. -/
theorem prime_product_unique (p₁ p₂ q₁ q₂ : ℕ)
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
    (hq₁ : Nat.Prime q₁) (hq₂ : Nat.Prime q₂)
    (h : p₁ * q₁ = p₂ * q₂) :
    (p₁ = p₂ ∧ q₁ = q₂) ∨ (p₁ = q₂ ∧ q₁ = p₂) := by sorry

end Erdos490Aristotle
