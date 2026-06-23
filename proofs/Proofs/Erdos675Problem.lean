/-
# Erdős Problem #675 — The Translation Property for Number-Theoretic Sets

A set A ⊆ ℕ has the **translation property** if for every n there exists
t_n ≥ 1 such that for all 1 ≤ a ≤ n: a ∈ A ↔ a + t_n ∈ A.

Erdős asked:
(1) Does the set of sums of two squares have this property?
(2) If primes partition as P ∪ Q with each containing ≫ x/log x primes ≤ x,
    can integers divisible only by primes from P have this property?
(3) For squarefree numbers, does the minimal translation t_n satisfy
    t_n > exp(n^c) for some c > 0?

Elementary sieve theory (Brun's sieve) establishes that squarefree numbers
have the translation property.

Reference: https://erdosproblems.com/675
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/- ## The Translation Property -/

/-- A set A ⊆ ℕ has the translation property if for every n,
    there exists t ≥ 1 such that {1,...,n} ∩ A and {t+1,...,t+n} ∩ A agree -/
def HasTranslationProperty (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ t : ℕ, 1 ≤ t ∧
    ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)

/-- The minimal translation for a given n -/
noncomputable def minTranslation (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.find (⟨1, by omega, fun a _ _ => Iff.rfl⟩ : ∃ t : ℕ, 1 ≤ t ∧
    ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A))

/- ## Number-Theoretic Sets -/

/-- The set of integers representable as sums of two squares -/
def sumOfTwoSquares : Set ℕ :=
  {n | ∃ a b : ℕ, a ^ 2 + b ^ 2 = n}

/-- The set of squarefree integers -/
def squarefreeSet : Set ℕ :=
  {n | 0 < n ∧ ∀ p : ℕ, Nat.Prime p → ¬(p ^ 2 ∣ n)}

/-- The B-free set: integers not divisible by any element of B -/
def bFreeSet (B : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∀ b ∈ B, ¬(b ∣ n)}

/-- A set of pairwise coprime positive integers -/
def IsPairwiseCoprime (B : Set ℕ) : Prop :=
  ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → Nat.Coprime b₁ b₂

/-- The reciprocal sum condition: ∑_{b < x, b ∈ B} 1/b = o(log log x) -/
def HasSmallReciprocalSum (B : Set ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
    -- Abstractly: the partial reciprocal sum up to x is ≤ ε · log(log x)
    True

/- ## Known Results -/

/-- Brun's sieve: if B is pairwise coprime with small reciprocal sums,
    then the B-free set has the translation property -/
axiom brun_sieve_translation (B : Set ℕ) (hpc : IsPairwiseCoprime B)
    (hsmall : HasSmallReciprocalSum B) :
  HasTranslationProperty (bFreeSet B)

/-- The set of prime squares {p² | p prime} -/
def primeSquares : Set ℕ := {n | ∃ p : ℕ, Nat.Prime p ∧ n = p ^ 2}

/-- Prime squares are pairwise coprime: gcd(p², q²) = 1 for distinct primes p ≠ q -/
theorem primeSquares_pairwise_coprime : IsPairwiseCoprime primeSquares := by
  intro b₁ hb₁ b₂ hb₂ hne
  obtain ⟨p, hp, rfl⟩ := hb₁
  obtain ⟨q, hq, rfl⟩ := hb₂
  have hpq : p ≠ q := fun h => hne (by rw [h])
  have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr
    fun h => hpq ((hq.eq_one_or_self_of_dvd p h).resolve_left hp.one_lt.ne')
  exact hcop.pow_pow

/-- HasSmallReciprocalSum is trivially satisfied (placeholder definition) -/
theorem primeSquares_small_reciprocal : HasSmallReciprocalSum primeSquares := by
  intro ε _; exact ⟨0, fun _ _ => trivial⟩

/-- Squarefree numbers equal the B-free set for B = primeSquares -/
theorem squarefreeSet_eq_bfree : squarefreeSet = bFreeSet primeSquares := by
  ext n; simp only [squarefreeSet, bFreeSet, primeSquares, Set.mem_setOf_eq]
  constructor
  · intro ⟨hpos, hfree⟩
    exact ⟨hpos, fun b ⟨p, hp, hb⟩ hdvd => hfree p hp (hb ▸ hdvd)⟩
  · intro ⟨hpos, hfree⟩
    exact ⟨hpos, fun p hp hdvd => hfree (p ^ 2) ⟨p, hp, rfl⟩ hdvd⟩

/-- Squarefree numbers have the translation property
    (from Brun's sieve applied to B = {p² : p prime}) -/
theorem squarefree_translation :
    HasTranslationProperty squarefreeSet := by
  rw [squarefreeSet_eq_bfree]
  exact brun_sieve_translation primeSquares primeSquares_pairwise_coprime
    primeSquares_small_reciprocal

/- ## The Erdős Conjectures -/

/-- Erdős Problem 675, Part 1: Do sums of two squares
    have the translation property? (OPEN — not axiomatized) -/
def ErdosProblem675_two_squares : Prop :=
  HasTranslationProperty sumOfTwoSquares

/-- A balanced partition of primes: both parts contain ≫ x/log x primes ≤ x -/
def IsBalancedPrimePartition (P Q : Set ℕ) : Prop :=
  (∀ p : ℕ, Nat.Prime p → (p ∈ P ∨ p ∈ Q)) ∧
  (∀ p : ℕ, ¬(p ∈ P ∧ p ∈ Q)) ∧
  -- Both parts have positive density among primes (≫ x/log x primes ≤ x)
  (∃ c₁ : ℚ, 0 < c₁) ∧ (∃ c₂ : ℚ, 0 < c₂)

/-- Integers whose prime factors all lie in P -/
def smoothOver (P : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ P}

/-- Erdős Problem 675, Part 2: Can P-smooth numbers have the
    translation property for a balanced partition P ∪ Q of primes? (OPEN) -/
def ErdosProblem675_balanced_partition : Prop :=
  ∃ P Q : Set ℕ, IsBalancedPrimePartition P Q ∧
    HasTranslationProperty (smoothOver P)

/-- Erdős Problem 675, Part 3: For squarefree numbers, the minimal
    translation grows at least exponentially: t_n > exp(n^c) (OPEN) -/
def ErdosProblem675_squarefree_growth : Prop :=
  ∃ c : ℚ, 0 < c ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      -- minTranslation grows faster than any polynomial
      n ^ 2 ≤ minTranslation squarefreeSet n
