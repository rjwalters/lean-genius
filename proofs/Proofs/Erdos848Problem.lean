/-
# Erdős Problem #848: Squarefree Products and Extremal Sets

Determine the maximum size of A ⊆ {1,...,N} such that ab + 1 is never
squarefree for all a, b ∈ A (including a = b).

Equivalently: for every a, b ∈ A, there exists a prime p with p² | ab + 1.

The conjectured extremal sets are {n ≡ 7 (mod 25)} and {n ≡ 18 (mod 25)},
each giving |A| ≈ N/25.

Solved by Sawhney for sufficiently large N.

Reference: https://erdosproblems.com/848
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

/- ## Definitions -/

/-- n is squarefree if no prime squared divides n. -/
def IsSquarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p * p ∣ n)

/-- A set A ⊆ {1,...,N} has the non-squarefree product property if
    ab + 1 is not squarefree for all a, b ∈ A. -/
def HasNonSqfreeProductProp (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬IsSquarefree (a * b + 1)

/-- The maximum size of a subset of {1,...,N} with the non-squarefree
    product property. Axiomatized. -/
axiom maxNonSqfreeSet (N : ℕ) : ℕ

/-- The max size is at most N. -/
axiom maxNonSqfreeSet_le (N : ℕ) : maxNonSqfreeSet N ≤ N

/- ## Known Results -/

/-- The set {n ∈ {1,...,N} : n ≡ 7 (mod 25)} achieves the property:
    for a ≡ b ≡ 7 (mod 25), ab + 1 ≡ 50 ≡ 0 (mod 25), so 5² | ab + 1. -/
theorem mod25_achieves :
  ∀ a b : ℕ, a % 25 = 7 → b % 25 = 7 →
    5 * 5 ∣ a * b + 1 := by
  intro a b ha hb
  -- Write a = 25q₁ + 7 and b = 25q₂ + 7 via the division algorithm
  have ha' : a = 25 * (a / 25) + 7 := by omega
  have hb' : b = 25 * (b / 25) + 7 := by omega
  rw [ha', hb']
  -- (25q₁ + 7)(25q₂ + 7) + 1 = 625q₁q₂ + 175q₁ + 175q₂ + 50
  --                             = 25(25q₁q₂ + 7q₁ + 7q₂ + 2)
  exact ⟨25 * (a / 25) * (b / 25) + 7 * (a / 25) + 7 * (b / 25) + 2, by ring⟩

/-- The symmetric case: {n ≡ 18 (mod 25)} also achieves the property.
    For a ≡ b ≡ 18 (mod 25), ab + 1 ≡ 325 ≡ 0 (mod 25), so 5² | ab + 1. -/
theorem mod25_achieves_18 :
  ∀ a b : ℕ, a % 25 = 18 → b % 25 = 18 →
    5 * 5 ∣ a * b + 1 := by
  intro a b ha hb
  have ha' : a = 25 * (a / 25) + 18 := by omega
  have hb' : b = 25 * (b / 25) + 18 := by omega
  rw [ha', hb']
  -- (25q₁ + 18)(25q₂ + 18) + 1 = 625q₁q₂ + 450q₁ + 450q₂ + 325
  --                               = 25(25q₁q₂ + 18q₁ + 18q₂ + 13)
  exact ⟨25 * (a / 25) * (b / 25) + 18 * (a / 25) + 18 * (b / 25) + 13, by ring⟩

/-- 5 is prime — needed to connect 5² | n to ¬IsSquarefree n. -/
theorem five_prime : Nat.Prime 5 := by decide

/-- If 5² | n, then n is not squarefree (by our definition). -/
theorem not_sqfree_of_five_sq_dvd {n : ℕ} (h : 5 * 5 ∣ n) : ¬IsSquarefree n := by
  intro hsf
  exact hsf 5 five_prime h

/-- The mod 7 residue class satisfies the full non-squarefree product property. -/
theorem mod7_set_has_property (A : Finset ℕ) (hA : ∀ a ∈ A, a % 25 = 7) :
    HasNonSqfreeProductProp A := by
  intro a ha b hb
  exact not_sqfree_of_five_sq_dvd (mod25_achieves a b (hA a ha) (hA b hb))

/-- The mod 18 residue class satisfies the full non-squarefree product property. -/
theorem mod18_set_has_property (A : Finset ℕ) (hA : ∀ a ∈ A, a % 25 = 18) :
    HasNonSqfreeProductProp A := by
  intro a ha b hb
  exact not_sqfree_of_five_sq_dvd (mod25_achieves_18 a b (hA a ha) (hA b hb))

/-- This gives a lower bound: maxNonSqfreeSet(N) ≥ ⌊N/25⌋. -/
axiom lower_bound (N : ℕ) (hN : 25 ≤ N) :
  N / 25 ≤ maxNonSqfreeSet N

/-- Van Doorn's upper bound: |A|/N ≤ 2 Σ_{p ≡ 1 (4)} 1/p² ≈ 0.108.
    So maxNonSqfreeSet(N) ≤ ⌊0.108 · N⌋ + O(1). -/
axiom vanDoorn_upper_bound :
  ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N →
    maxNonSqfreeSet N * 1000 ≤ 108 * N + C

/- ## The Solution -/

/-- Sawhney's theorem: for sufficiently large N, the maximum is exactly
    ⌊N/25⌋, achieved only by {n ≡ 7 (mod 25)} or {n ≡ 18 (mod 25)}. -/
axiom sawhney_solution :
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    maxNonSqfreeSet N = N / 25

/-- Structural result: any extremal set for large N is contained in
    {n ≡ 7 (mod 25)} or {n ≡ 18 (mod 25)}. -/
axiom sawhney_structure :
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      HasNonSqfreeProductProp A → A.card = N / 25 →
        (∀ a ∈ A, a % 25 = 7) ∨ (∀ a ∈ A, a % 25 = 18)
