/-
  Aristotle targets for Erdos490Problem
  Routine supporting lemmas for automated proof search.
  See Erdos490Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT szemeredi_theorem: deep combinatorial bound (axiomatized)
  - NOT optimal_has_distinct_products: axiomatized
  - NOT distinct_minimal_energy: complex bijectivity argument
  - NOT primes_sidon: requires computing product set cardinality
  - NOT bound_is_optimal (lower bound part): requires prime counting
  - Subset membership checks: provable from filter definitions by simp/omega
  - Distinct-product criterion for primes: elementary number theory

  Included targets (3):
  - optimalA_is_subset_ari: optimalA N ⊆ {1,...,N} by definition
  - optimalB_is_subset_ari: optimalB N ⊆ {1,...,N} by definition
  - optimal_works_because_primes_ari: a₁p₁ = a₂p₂ with primes p₁,p₂ > N/2
      and a₁,a₂ ≤ N/2 implies a₁ = a₂ ∧ p₁ = p₂

  NOT included:
  - szemeredi_theorem: axiomatized (deep result)
  - optimal_has_distinct_products: axiomatized
  - erdos_678_infinitely_many / cambie_2024: requires analytic number theory
  - distinct_minimal_energy: cardinality/bijectivity reasoning
  - Lower bound in bound_is_optimal: requires prime number theorem asymptotics
-/
import Mathlib
import Proofs.Erdos490Problem

namespace Erdos490Aristotle

open Finset Erdos490

/-
## Section: Subset Membership for Optimal Example Sets

optimalA N = {n ∈ {0,...,N} | 1 ≤ n ∧ n ≤ N/2}
optimalB N = {p ∈ {0,...,N} | Prime p ∧ N/2 < p ∧ p ≤ N}

Both are subsets of {1,...,N} by their filter conditions.

Key Mathlib lemmas:
- Finset.mem_filter: p ∈ filter f s ↔ p ∈ s ∧ f p
- Nat.div_le_self: N / 2 ≤ N
- Nat.Prime.one_le: prime p → 1 ≤ p
-/

/-- Every element of optimalA N lies in {1,...,N}.
    The filter condition n ≤ N/2 implies n ≤ N since N/2 ≤ N. -/
theorem optimalA_is_subset_ari (N : ℕ) :
    IsSubsetUpTo (optimalA N) N := by
  intro a ha
  simp only [optimalA, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨_, h1, h2⟩ := ha
  exact ⟨h1, Nat.le_trans h2 (Nat.div_le_self N 2)⟩

/-- Every element of optimalB N lies in {1,...,N}.
    The filter conditions give primality (→ a ≥ 2 ≥ 1) and p ≤ N. -/
theorem optimalB_is_subset_ari (N : ℕ) :
    IsSubsetUpTo (optimalB N) N := by
  intro p hp
  simp only [optimalB, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨_, hprime, _, hle⟩ := hp
  exact ⟨hprime.one_le, hle⟩

/-
## Section: Distinct Products via Prime Divisibility

If a₁ · p₁ = a₂ · p₂ where p₁, p₂ are primes both exceeding N/2,
and a₁, a₂ ≤ N/2, then a₁ = a₂ and p₁ = p₂.

Proof:
1. p₁ | a₁ · p₁ = a₂ · p₂, so p₁ | a₂ · p₂.
2. Since p₁ is prime: p₁ | a₂ ∨ p₁ | p₂.
3. If p₁ | a₂: then a₂ ≥ p₁ > N/2 ≥ a₂, contradiction.
4. So p₁ | p₂. Since p₂ is prime and p₁ ≥ 2: p₁ = p₂.
5. Cancel p₁ to get a₁ = a₂.

Key Mathlib lemmas:
- Nat.Prime.dvd_mul: prime p → p ∣ a * b → p ∣ a ∨ p ∣ b
- Nat.Prime.eq_of_dvd_of_prime: prime p → prime q → p ∣ q → p = q
- Nat.le_of_dvd: 0 < n → m ∣ n → m ≤ n
- Nat.mul_left_cancel: cancellation for multiplication
-/

/-- Products a·p are distinct when p is a prime exceeding all elements of A.
    This justifies the construction in the optimal example for Problem #490. -/
theorem optimal_works_because_primes_ari (N a₁ a₂ p₁ p₂ : ℕ)
    (ha₁ : a₁ ≤ N / 2) (ha₂ : a₂ ≤ N / 2)
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
    (hp₁_large : N / 2 < p₁) (hp₂_large : N / 2 < p₂)
    (heq : a₁ * p₁ = a₂ * p₂) : a₁ = a₂ ∧ p₁ = p₂ := by
  -- p₁ divides a₁ * p₁ = a₂ * p₂
  have hdvd : p₁ ∣ a₂ * p₂ := heq ▸ dvd_mul_left p₁ a₁
  -- Since p₁ is prime: p₁ | a₂ ∨ p₁ | p₂
  rcases hp₁.dvd_mul.mp hdvd with h | h
  · -- Case p₁ | a₂: but then a₂ ≥ p₁ > N/2 ≥ a₂, contradiction
    have : p₁ ≤ a₂ := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
      intro ha₂z; simp [ha₂z] at heq; exact hp₁.ne_zero (Nat.eq_zero_of_mul_eq_zero_left heq))) h
    omega
  · -- Case p₁ | p₂: since both are prime, p₁ = p₂
    have heqp : p₁ = p₂ := (hp₁.eq_of_dvd_of_prime hp₂ h).symm ▸ rfl
    -- Cancel to get a₁ = a₂
    have heqa : a₁ = a₂ := Nat.eq_of_mul_eq_mul_right hp₁.pos (heqp ▸ heq)
    exact ⟨heqa, heqp⟩

end Erdos490Aristotle
