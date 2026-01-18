/-
Erdős Problem #418: Non-Cototients

Source: https://erdosproblems.com/418
Status: SOLVED by Browkin and Schinzel (1995)

Statement:
Are there infinitely many positive integers not of the form n - φ(n)?

Answer: YES - Integers of the form 2^k · 509203 (k ≥ 1) are non-cototients.

Key Definitions:
- φ(n) is Euler's totient function (count of integers ≤ n coprime to n)
- A "cototient" of n is n - φ(n)
- A "non-cototient" is a number that is NOT a cototient for any n

Known Results:
- Browkin-Schinzel (1995): 2^k · 509203 are non-cototients for all k ≥ 1
- Conditional on Goldbach: Every odd number is a cototient
- Open: Does the set of non-cototients have positive density?

References:
- [BrSc95] Browkin & Schinzel, "On integers not of the form n - φ(n)" (1995)
- [Er73b] Erdős, "Über die Zahlen der Form σ(n) - n und n - φ(n)" (1973)
- OEIS A005278 (non-cototients)
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open Nat

namespace Erdos418

/-!
## Part I: Core Definitions

The cototient of n is n - φ(n), which counts the integers from 1 to n
that share a common factor with n.
-/

/-- The cototient of n: the count of integers ≤ n that share a factor with n.
    cototient(n) = n - φ(n). -/
def cototient (n : ℕ) : ℕ := n - n.totient

/-- A number m is a cototient-value if m = n - φ(n) for some n.
    These are the numbers in the "range" of the cototient function. -/
def IsCototientValue (m : ℕ) : Prop :=
  ∃ n : ℕ, cototient n = m

/-- A non-cototient is a positive integer that is NOT a cototient value.
    These are numbers that cannot be expressed as n - φ(n) for any n. -/
def IsNonCototient (m : ℕ) : Prop :=
  m > 0 ∧ ¬IsCototientValue m

/-- The set of all cototient values: { n - φ(n) | n ∈ ℕ }. -/
def CototientValues : Set ℕ :=
  { m | IsCototientValue m }

/-- The set of all non-cototients. -/
def NonCototients : Set ℕ :=
  { m | IsNonCototient m }

/-!
## Part II: Basic Properties of Cototient
-/

/-- cototient(1) = 1 - φ(1) = 1 - 1 = 0. -/
theorem cototient_one : cototient 1 = 0 := by
  simp [cototient, Nat.totient_one]

/-- cototient(2) = 2 - φ(2) = 2 - 1 = 1. -/
theorem cototient_two : cototient 2 = 1 := by
  native_decide

/-- cototient(p) = p - φ(p) = p - (p-1) = 1 for prime p. -/
theorem cototient_prime (p : ℕ) (hp : p.Prime) : cototient p = 1 := by
  simp only [cototient, Nat.totient_prime hp]
  have h2 : 2 ≤ p := hp.two_le
  omega

/-- cototient(4) = 4 - φ(4) = 4 - 2 = 2. -/
example : cototient 4 = 2 := by native_decide

/-- cototient(6) = 6 - φ(6) = 6 - 2 = 4. -/
example : cototient 6 = 4 := by native_decide

/-- cototient(9) = 9 - φ(9) = 9 - 6 = 3. -/
example : cototient 9 = 3 := by native_decide

/-!
## Part III: Small Cototient Values

Let's verify which small numbers are cototient values.
-/

/-- 0 is a cototient value: 0 = cototient(1). -/
theorem zero_is_cototient : IsCototientValue 0 := ⟨1, cototient_one⟩

/-- 1 is a cototient value: 1 = cototient(2). -/
theorem one_is_cototient : IsCototientValue 1 := ⟨2, cototient_two⟩

/-- 2 is a cototient value: 2 = cototient(4). -/
theorem two_is_cototient : IsCototientValue 2 := ⟨4, by native_decide⟩

/-- 3 is a cototient value: 3 = cototient(9). -/
theorem three_is_cototient : IsCototientValue 3 := ⟨9, by native_decide⟩

/-- 4 is a cototient value: 4 = cototient(6) or cototient(8). -/
theorem four_is_cototient : IsCototientValue 4 := ⟨8, by native_decide⟩

/-!
## Part IV: The First Non-Cototient

The smallest non-cototient is 10. No n satisfies n - φ(n) = 10.
-/

/-- 10 is the smallest non-cototient. We state this as an axiom since
    proving it requires checking all n. -/
axiom ten_is_non_cototient : IsNonCototient 10

/-- The list of small non-cototients (OEIS A005278):
    10, 26, 34, 50, 52, 58, 86, 100, ... -/
axiom small_non_cototients :
    IsNonCototient 10 ∧ IsNonCototient 26 ∧ IsNonCototient 34 ∧
    IsNonCototient 50 ∧ IsNonCototient 52 ∧ IsNonCototient 58

/-!
## Part V: The Main Theorem (SOLVED)

Browkin and Schinzel proved there are infinitely many non-cototients.
-/

/-- The magic number from Browkin-Schinzel: 509203.
    All numbers of the form 2^k · 509203 (k ≥ 1) are non-cototients. -/
def browkinSchinzelBase : ℕ := 509203

/-- The Browkin-Schinzel witness sequence: 2^(k+1) · 509203. -/
def browkinSchinzelWitness (k : ℕ) : ℕ := 2^(k + 1) * browkinSchinzelBase

/-- Browkin-Schinzel (1995): All numbers 2^(k+1) · 509203 are non-cototients. -/
axiom browkin_schinzel_theorem :
    ∀ k : ℕ, IsNonCototient (browkinSchinzelWitness k)

/-- **Erdős Problem #418 (SOLVED)**: There are infinitely many non-cototients.

    Proof: The Browkin-Schinzel sequence 2^(k+1) · 509203 provides
    infinitely many distinct non-cototients. -/
axiom erdos_418 : NonCototients.Infinite

/-!
## Part VI: Conditional Result on Odd Numbers

Assuming a strengthened Goldbach conjecture (every even n > 6 is the sum
of two DISTINCT primes), every odd number is a cototient value.
-/

/-- Strengthened Goldbach: Every even n > 6 is a sum of two distinct primes. -/
def StrengthenedGoldbach : Prop :=
  ∀ n : ℕ, n > 6 → Even n → ∃ p q : ℕ, p ≠ q ∧ p.Prime ∧ q.Prime ∧ n = p + q

/-- Under strengthened Goldbach, every odd number is a cototient value.

    Proof idea: For odd m ≥ 7, m + 1 is even > 6, so m + 1 = p + q with
    p ≠ q prime. Then cototient(p·q) = p·q - φ(p·q) = p·q - (p-1)(q-1)
    = p·q - p·q + p + q - 1 = p + q - 1 = m. -/
axiom odd_cototient_conditional (hG : StrengthenedGoldbach) :
    ∀ m : ℕ, Odd m → IsCototientValue m

/-- The small odd cases: 1, 3, 5 are cototients.
    1 = cototient(2), 3 = cototient(9), 5 = cototient(25). -/
theorem small_odd_cototients :
    IsCototientValue 1 ∧ IsCototientValue 3 ∧ IsCototientValue 5 := by
  refine ⟨one_is_cototient, three_is_cototient, ?_⟩
  exact ⟨25, by native_decide⟩

/-!
## Part VII: Open Questions

It remains open whether non-cototients have positive density.
-/

/-- A set S ⊆ ℕ has positive lower density if
    liminf_{n→∞} |S ∩ [1,n]| / n > 0. -/
def HasPositiveDensity (S : Set ℕ) : Prop :=
  ∃ δ > 0, ∀ᶠ n in Filter.atTop,
    (S ∩ Finset.range (n + 1)).toFinite.toFinset.card ≥ δ * n

/-- **Open Question**: Do non-cototients have positive density?

    This is mentioned as open in the literature. The Browkin-Schinzel
    construction gives a sparse set (2^k · 509203), not positive density. -/
axiom density_open : True  -- Placeholder for open status

/-!
## Part VIII: Related Function σ(n) - n

A related problem concerns numbers not of the form σ(n) - n (nonaliquots).
Erdős showed these have positive density.
-/

/-- The aliquot sum: sum of proper divisors = σ(n) - n. -/
def aliquotSum (n : ℕ) : ℕ := (n.divisors.sum id) - n

/-- A non-aliquot is a number not expressible as σ(n) - n. -/
def IsNonAliquot (m : ℕ) : Prop :=
  m > 0 ∧ ∀ n : ℕ, aliquotSum n ≠ m

/-- **Erdős (1973)**: Non-aliquots have positive density.
    This is contrast with non-cototients where density is unknown. -/
axiom erdos_nonaliquot_density : ∃ S : Set ℕ, HasPositiveDensity S ∧
    ∀ m ∈ S, IsNonAliquot m

/-!
## Summary

**Erdős Problem #418** asks whether there are infinitely many non-cototients
(numbers not of the form n - φ(n)).

**Answer**: YES (Browkin-Schinzel 1995)

**Key Construction**: 2^(k+1) · 509203 are non-cototients for all k ≥ 0.

**Conditional Result**: Under strengthened Goldbach, all odd numbers are cototients.

**Open**: Do non-cototients have positive density?
-/

theorem erdos_418_summary :
    browkinSchinzelBase = 509203 ∧
    browkinSchinzelWitness 0 = 2 * 509203 ∧
    browkinSchinzelWitness 1 = 4 * 509203 := by
  simp only [browkinSchinzelBase, browkinSchinzelWitness]
  native_decide

end Erdos418
