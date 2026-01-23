/-
Erdős Problem #1059: Primes p where p - k! is Always Composite

**Statement**: Are there infinitely many primes p such that p - k! is composite
for all k with 1 ≤ k! < p?

**Status**: OPEN

**Examples**: p = 101, p = 211

Reference: https://erdosproblems.com/1059
Problem A2 in Guy's "Unsolved Problems in Number Theory"
-/

import Mathlib

open Nat BigOperators Finset

namespace Erdos1059

/-
## Part I: Basic Definitions
-/

/-- The k values to check: those where k! < p. -/
def validK (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun k => k.factorial < p ∧ k ≥ 1)

/-- A prime p has the property if p - k! is composite for all valid k. -/
def HasProperty (p : ℕ) : Prop :=
  p.Prime ∧ ∀ k ∈ validK p, ¬(p - k.factorial).Prime

/-- Equivalently: p - k! is composite (> 1 and not prime). -/
def HasPropertyStrong (p : ℕ) : Prop :=
  p.Prime ∧ ∀ k ∈ validK p, p - k.factorial > 1 ∧ ¬(p - k.factorial).Prime

/-
## Part II: Examples
-/

/-- p = 101 has the property.
    Valid k: 1 (1! = 1), 2 (2! = 2), 3 (3! = 6), 4 (4! = 24)
    (5! = 120 > 101)
    Check:
    - 101 - 1 = 100 = 4·25 (composite)
    - 101 - 2 = 99 = 9·11 (composite)
    - 101 - 6 = 95 = 5·19 (composite)
    - 101 - 24 = 77 = 7·11 (composite) -/
theorem example_101 : HasProperty 101 := by
  constructor
  · norm_num
  · intro k hk
    simp only [validK, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, hfact, hk1⟩ := hk
    interval_cases k
    all_goals simp only [Nat.factorial]; norm_num

/-- Verification for 101. -/
example : ¬Nat.Prime 100 := by native_decide
example : ¬Nat.Prime 99 := by native_decide
example : ¬Nat.Prime 95 := by native_decide
example : ¬Nat.Prime 77 := by native_decide

/-- p = 211 has the property.
    Valid k: 1, 2, 3, 4, 5 (5! = 120 < 211, 6! = 720 > 211)
    Check:
    - 211 - 1 = 210 = 2·105 (composite)
    - 211 - 2 = 209 = 11·19 (composite)
    - 211 - 6 = 205 = 5·41 (composite)
    - 211 - 24 = 187 = 11·17 (composite)
    - 211 - 120 = 91 = 7·13 (composite) -/
theorem example_211 : HasProperty 211 := by
  constructor
  · norm_num
  · intro k hk
    simp only [validK, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, hfact, hk1⟩ := hk
    interval_cases k
    all_goals simp only [Nat.factorial]; norm_num

/-- Verification for 211. -/
example : ¬Nat.Prime 210 := by native_decide
example : ¬Nat.Prime 209 := by native_decide
example : ¬Nat.Prime 205 := by native_decide
example : ¬Nat.Prime 187 := by native_decide
example : ¬Nat.Prime 91 := by native_decide

/-
## Part III: The Main Conjecture
-/

/-- Main conjecture: There are infinitely many such primes. -/
def mainConjecture : Prop := Set.Infinite {p : ℕ | HasProperty p}

/-- Known examples. -/
def knownExamples : List ℕ := [101, 211]

/-
## Part IV: Erdős's Weaker Variant
-/

/-- Erdős suggested a possibly easier variant:
    Infinitely many n where l! < n ≤ (l+1)! and:
    1. All prime factors of n are > l
    2. n - k! is composite for all 1 ≤ k ≤ l -/
def HasWeakProperty (n : ℕ) : Prop :=
  ∃ l : ℕ, l.factorial < n ∧ n ≤ (l + 1).factorial ∧
    (∀ p : ℕ, p.Prime → p ∣ n → p > l) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ l → ¬(n - k.factorial).Prime)

/-- Weaker conjecture. -/
def weakerConjecture : Prop := Set.Infinite {n : ℕ | HasWeakProperty n}

/-
## Part V: Observations
-/

/-- For a prime p to have the property, it must avoid p - k! being prime
    for several values of k. Since k! grows fast, this is finitely many checks. -/
theorem finite_checks (p : ℕ) (hp : p.Prime) :
    (validK p).card ≤ Nat.log 2 p + 3 := by
  sorry

/-- If p ≡ 1 (mod 6), then p - 1 = 0 (mod 6), so p - 1! is even ≥ 6,
    hence composite. This gives us one "free" k. -/
theorem mod6_helps (p : ℕ) (hp : p.Prime) (hp6 : p % 6 = 1) (hp2 : p > 3) :
    ¬(p - 1).Prime := by
  have : (p - 1) % 6 = 0 := by omega
  sorry

/-
## Part VI: Summary
-/

/-- Erdős Problem #1059: Summary

    **Definition**: Prime p has property if p - k! composite for all 1 ≤ k! < p.

    **Examples**: 101, 211 (verified).

    **Key Insight**: Fast growth of k! means only ~log p values to check.

    **Weaker variant** (Erdős): n in (l!, (l+1)!] with all prime factors > l
    and all n - k! composite.

    **Status**: Both conjectures OPEN. -/
theorem erdos_1059_summary :
    -- Examples exist
    HasProperty 101 ∧ HasProperty 211 := by
  exact ⟨example_101, example_211⟩

end Erdos1059
