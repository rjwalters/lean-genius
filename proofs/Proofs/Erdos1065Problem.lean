/-
Erdős Problem #1065: Primes of the Form 2^k·q + 1

**Statement**: Are there infinitely many primes p such that p = 2^k·q + 1
for some prime q and k ≥ 0? Or primes of the form p = 2^k·3^l·q + 1?

**Status**: OPEN

Reference: https://erdosproblems.com/1065
Problem B46 in Guy's "Unsolved Problems in Number Theory"
-/

import Mathlib

open Nat BigOperators Finset

namespace Erdos1065

/-
## Part I: First Form (2^k·q + 1)
-/

/-- A prime p has "form 1" if p = 2^k·q + 1 for some prime q and k ≥ 0. -/
def HasForm1 (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k q : ℕ, q.Prime ∧ p = 2^k * q + 1

/-- Equivalently: p-1 = 2^k·q for some prime q. -/
def HasForm1' (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k q : ℕ, q.Prime ∧ p - 1 = 2^k * q

/-- The two definitions are equivalent for p > 1. -/
theorem form1_equiv (p : ℕ) (hp : p > 1) : HasForm1 p ↔ HasForm1' p := by
  constructor
  · intro ⟨hprime, k, q, hq, heq⟩
    refine ⟨hprime, k, q, hq, ?_⟩
    omega
  · intro ⟨hprime, k, q, hq, heq⟩
    refine ⟨hprime, k, q, hq, ?_⟩
    omega

/-- The main conjecture for form 1. -/
def conjecture1 : Prop := Set.Infinite {p : ℕ | HasForm1 p}

/-
## Part II: Second Form (2^k·3^l·q + 1)
-/

/-- A prime p has "form 2" if p = 2^k·3^l·q + 1 for some prime q and k,l ≥ 0. -/
def HasForm2 (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k l q : ℕ, q.Prime ∧ p = 2^k * 3^l * q + 1

/-- Equivalently: p-1 = 2^k·3^l·q for some prime q. -/
def HasForm2' (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k l q : ℕ, q.Prime ∧ p - 1 = 2^k * 3^l * q

/-- The main conjecture for form 2. -/
def conjecture2 : Prop := Set.Infinite {p : ℕ | HasForm2 p}

/-
## Part III: Examples
-/

/-- 3 has form 1: 3 = 2^0·2 + 1 = 2 + 1. -/
theorem form1_3 : HasForm1 3 := by
  refine ⟨Nat.prime_three, 0, 2, Nat.prime_two, ?_⟩
  norm_num

/-- 5 has form 1: 5 = 2^2·1 + 1? No, 1 is not prime. 5 = 2^1·2 + 1 = 4 + 1 = 5. ✓ -/
theorem form1_5 : HasForm1 5 := by
  refine ⟨Nat.prime_five, 1, 2, Nat.prime_two, ?_⟩
  norm_num

/-- 7 has form 1: 7 = 2^1·3 + 1 = 6 + 1 = 7. ✓ -/
theorem form1_7 : HasForm1 7 := by
  refine ⟨by norm_num, 1, 3, Nat.prime_three, ?_⟩
  norm_num

/-- 11 has form 1: 11 = 2^1·5 + 1 = 10 + 1 = 11. ✓ -/
theorem form1_11 : HasForm1 11 := by
  refine ⟨by norm_num, 1, 5, by norm_num, ?_⟩
  norm_num

/-- 13 has form 1: 13 = 2^2·3 + 1 = 12 + 1 = 13. ✓ -/
theorem form1_13 : HasForm1 13 := by
  refine ⟨by norm_num, 2, 3, Nat.prime_three, ?_⟩
  norm_num

/-- 17 has form 1: 17 = 2^4·1 + 1? No. 17 - 1 = 16 = 2^4, no odd prime factor.
    So 17 does NOT have form 1! -/
theorem not_form1_17 : ¬HasForm1 17 := by
  intro ⟨_, k, q, hq, heq⟩
  have h16 : 17 - 1 = 16 := by norm_num
  have : 16 = 2^k * q := by omega
  interval_cases k
  · simp at this; omega
  · simp at this; have : q = 8 := by omega; simp_all
  · simp at this; have : q = 4 := by omega; simp_all
  · simp at this; have : q = 2 := by omega
    subst this; simp at heq
  · simp at this; have : q = 1 := by omega; simp_all

/-- 19 has form 1: 19 = 2^1·9 + 1? 9 not prime. 19 = 2^0·18 + 1? 18 not prime.
    19 - 1 = 18 = 2·9 = 2·3². No odd prime to single power.
    Actually: 18 = 2·3·3, so form 2 works with q=3 but form 1 needs single prime.
    19 does NOT have form 1. -/
theorem not_form1_19 : ¬HasForm1 19 := by
  intro ⟨_, k, q, hq, heq⟩
  have h18 : 19 - 1 = 18 := by norm_num
  have : 18 = 2^k * q := by omega
  interval_cases k
  · simp at this; have : q = 18 := by omega
    subst this
    have : ¬(18 : ℕ).Prime := by decide
    contradiction
  · simp at this; have : q = 9 := by omega
    subst this
    have : ¬(9 : ℕ).Prime := by decide
    contradiction
  · simp at this; omega
  all_goals simp at this; omega

/-- 19 has form 2: 19 = 2^1·3^2·1 + 1? 1 not prime. 19 = 2^1·3^1·3 + 1 = 18 + 1. ✓ -/
theorem form2_19 : HasForm2 19 := by
  refine ⟨by norm_num, 1, 1, 3, Nat.prime_three, ?_⟩
  norm_num

/-
## Part IV: Structure of p-1
-/

/-- For form 1, p-1 must have exactly one odd prime factor (with multiplicity 1). -/
def HasSingleOddPrimeFactor (n : ℕ) : Prop :=
  ∃ k q : ℕ, q.Prime ∧ q % 2 = 1 ∧ n = 2^k * q

/-- Form 1 means p-1 has a single odd prime factor. -/
theorem form1_structure (p : ℕ) (hp : p.Prime) (hp2 : p > 2) :
    HasForm1 p ↔ HasSingleOddPrimeFactor (p - 1) := by
  sorry

/-
## Part V: Summary
-/

/-- Erdős Problem #1065: Summary

    **Form 1**: p = 2^k·q + 1 (p-1 = 2^k times odd prime)
    - Examples: 3, 5, 7, 11, 13, 23, 29, 37, ...
    - Non-examples: 17 (p-1 = 16 = 2^4), 19 (p-1 = 18 = 2·3²)

    **Form 2**: p = 2^k·3^l·q + 1 (more flexible, allows 3's)
    - Includes all form 1 primes (take l=0)
    - Also includes 19 (p-1 = 18 = 2·3·3)

    **Open**: Are there infinitely many of each form? -/
theorem erdos_1065_summary :
    -- Many small primes have form 1
    HasForm1 3 ∧ HasForm1 5 ∧ HasForm1 7 ∧ HasForm1 11 ∧ HasForm1 13 ∧
    -- But not all (17, 19 fail)
    ¬HasForm1 17 ∧ ¬HasForm1 19 ∧
    -- 19 does have form 2
    HasForm2 19 := by
  refine ⟨form1_3, form1_5, form1_7, form1_11, form1_13,
          not_form1_17, not_form1_19, form2_19⟩

end Erdos1065
