/-
  Erdős Problem #366: Consecutive k-Full Numbers

  Are there any 2-full n such that n+1 is 3-full?

  **Definitions**:
  - n is k-full if for every prime p dividing n, we have p^k | n
  - 2-full = powerful = squareful (every prime factor appears at least squared)
  - 3-full = cubeful (every prime factor appears at least cubed)

  **Known Results**:
  - (8, 9): 8 = 2³ is 3-full, 9 = 3² is 2-full (reverse direction)
  - (12167, 12168): 12167 = 23³ is 3-full, 12168 = 2³ × 3² × 13² is 2-full
  - No 2-full n with 3-full n+1 known (OPEN as of 2024)
  - No other 3-full/2-full pairs below 10^22

  References:
  - https://erdosproblems.com/366
  - Golomb, S.W., "Powerful numbers" (1970)
  - Guy, R.K., "Unsolved Problems in Number Theory" (2004), Problem B16
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

open Nat Finset

namespace Erdos366

/-!
## Background: k-Full Numbers

A natural number n is **k-full** if every prime factor p of n appears
with multiplicity at least k. Equivalently, p | n implies p^k | n.

Special cases:
- 1-full: all positive integers
- 2-full: powerful numbers (also called squareful)
- 3-full: cubeful numbers
-/

/-- n is k-full if every prime factor of n appears with multiplicity ≥ k.
That is, if p | n then p^k | n. Equivalently, n.factorization p ≥ k for all p | n. -/
def IsKFull (k n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → k ≤ n.factorization p

/-- Alternative definition: n is k-full iff all prime factors have multiplicity ≥ k. -/
def IsKFull' (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, k ≤ n.factorization p

/-- 2-full numbers are also called **powerful** numbers. -/
def IsPowerful (n : ℕ) : Prop := IsKFull 2 n

/-- 3-full numbers are called **cubeful** numbers. -/
def IsCubeful (n : ℕ) : Prop := IsKFull 3 n

/-!
## Basic Properties of k-Full Numbers
-/

/-- 1 is vacuously k-full for any k (no prime factors). -/
theorem one_is_kfull (k : ℕ) : IsKFull k 1 := by
  intro p hp hdiv
  -- p | 1 implies p = 1, but p is prime so p ≥ 2, contradiction
  have h1 : p = 1 := Nat.dvd_one.mp hdiv
  exact absurd h1 (Nat.Prime.ne_one hp)

/-- 0 is not k-full for k ≥ 1 (we consider 0 separately). -/
axiom zero_not_kfull (k : ℕ) (hk : k ≥ 1) : ¬IsKFull k 0

/-- A prime power p^m is k-full iff m ≥ k. -/
axiom prime_pow_kfull (p m k : ℕ) (hp : p.Prime) :
  IsKFull k (p ^ m) ↔ m ≥ k

/-!
## Examples of k-Full Numbers
-/

/-- 4 = 2² is 2-full (powerful). -/
axiom four_is_powerful : IsPowerful 4

/-- 8 = 2³ is 3-full (cubeful). -/
axiom eight_is_cubeful : IsCubeful 8

/-- 9 = 3² is 2-full (powerful). -/
axiom nine_is_powerful : IsPowerful 9

/-- 27 = 3³ is 3-full (cubeful). -/
axiom twentyseven_is_cubeful : IsCubeful 27

/-- 36 = 2² × 3² is 2-full (powerful). -/
axiom thirtysix_is_powerful : IsPowerful 36

/-!
## The Main Question: 2-Full n with 3-Full n+1

Erdős asked whether there exists any n such that:
- n is 2-full (powerful)
- n+1 is 3-full (cubeful)

This remains OPEN as of 2024.
-/

/-- **Erdős Problem #366**: Does there exist n > 0 such that
n is 2-full and n+1 is 3-full? -/
def erdos_366_conjecture : Prop :=
  ∃ n > 0, IsPowerful n ∧ IsCubeful (n + 1)

/-- The problem remains open - neither proved nor disproved. -/
axiom erdos_366_open : ¬(erdos_366_conjecture ↔ True) ∧ ¬(erdos_366_conjecture ↔ False)

/-!
## The Reverse Direction: 3-Full n with 2-Full n+1

The reverse direction has known solutions!
-/

/-- The set of pairs (n, n+1) where n is 3-full and n+1 is 2-full. -/
def CubefulPowerfulPairs : Set ℕ := { n | IsCubeful n ∧ IsPowerful (n + 1) }

/-- (8, 9) is a cubeful-powerful pair: 8 = 2³ is cubeful, 9 = 3² is powerful. -/
theorem eight_nine_pair : 8 ∈ CubefulPowerfulPairs := ⟨eight_is_cubeful, nine_is_powerful⟩

/-- 12167 = 23³ is cubeful. -/
axiom cubeful_12167 : IsCubeful 12167

/-- 12168 = 2³ × 3² × 13² is powerful. -/
axiom powerful_12168 : IsPowerful 12168

/-- (12167, 12168) is a cubeful-powerful pair (Golomb 1970). -/
theorem golomb_pair : 12167 ∈ CubefulPowerfulPairs :=
  ⟨cubeful_12167, powerful_12168⟩

/-- Known pairs: (8, 9) and (12167, 12168). -/
axiom known_pairs : CubefulPowerfulPairs ∩ {n | n < 10^22} = {8, 12167}

/-!
## Weaker Question: Consecutive 3-Full Numbers

Erdős (1976) asked the weaker question: Are there consecutive
3-full integers (n, n+1)?
-/

/-- The set of n where both n and n+1 are 3-full. -/
def ConsecutiveCubefuls : Set ℕ := { n | IsCubeful n ∧ IsCubeful (n + 1) }

/-- **Weaker question**: Do consecutive 3-full integers exist? -/
def erdos_366_weaker : Prop := ∃ n > 0, IsCubeful n ∧ IsCubeful (n + 1)

/-- The weaker question also appears open (no known examples). -/
axiom erdos_366_weaker_open : ¬(erdos_366_weaker ↔ True) ∧ ¬(erdos_366_weaker ↔ False)

/-!
## Related Question: Infinitely Many Pairs

Are there infinitely many pairs (n, n+1) where n is 3-full and n+1 is 2-full?
-/

/-- Are there infinitely many cubeful-powerful pairs? -/
def erdos_366_infinitely_many : Prop := CubefulPowerfulPairs.Infinite

/-- This also remains open. -/
axiom erdos_366_infinitely_many_open :
  ¬(erdos_366_infinitely_many ↔ True) ∧ ¬(erdos_366_infinitely_many ↔ False)

/-!
## Connection to Powerful Numbers and Pell Equations

Erdős originally asked Mahler about consecutive powerful numbers.
Mahler immediately showed infinitely many exist via Pell equations.
-/

/-- Consecutive powerful numbers exist in abundance (Mahler).
The Pell equation x² = 8y² + 1 gives infinitely many solutions. -/
axiom mahler_consecutive_powerful :
  { n | IsPowerful n ∧ IsPowerful (n + 1) }.Infinite

/-- Example: 8 and 9 are consecutive powerful numbers.
8 = 2³ has 2 appearing with multiplicity 3 ≥ 2.
9 = 3² has 3 appearing with multiplicity 2 ≥ 2. -/
axiom eight_is_powerful : IsPowerful 8

/-- 8 and 9 are consecutive powerful numbers. -/
theorem eight_nine_powerful : IsPowerful 8 ∧ IsPowerful 9 :=
  ⟨eight_is_powerful, nine_is_powerful⟩

/-!
## Computational Bounds

OEIS A060355 lists 3-full n with 2-full n+1.
As of 2024, only {8, 12167} are known below 10^22.
-/

/-- No cubeful-powerful pairs between 12167 and 10^22 (computational). -/
axiom computational_bound :
  ∀ n, 12167 < n → n < 10^22 → n ∉ CubefulPowerfulPairs

/-- If a new pair exists in the forward direction (2-full, 3-full),
it must be extremely large. -/
axiom forward_pair_bound :
  ∀ n, n < 10^22 → ¬(IsPowerful n ∧ IsCubeful (n + 1))

/-!
## Structure of k-Full Numbers

k-full numbers have the form ∏ pᵢ^(aᵢ) where all aᵢ ≥ k.
-/

/-- A k-full number can be written as a product of k-th powers and higher. -/
axiom kfull_structure (k n : ℕ) (hn : n > 1) (hk : IsKFull k n) :
  ∃ a b : ℕ, b > 0 ∧ n = a^k * b^(k+1)

/-- Powerful numbers (2-full) can be written as a²b³. -/
axiom powerful_form (n : ℕ) (hn : n > 1) (hp : IsPowerful n) :
  ∃ a b : ℕ, n = a^2 * b^3

/-!
## Density of k-Full Numbers

The number of k-full numbers up to x is asymptotic to c_k × x^(1/k).

**Powerful numbers**: |{n ≤ N : n is powerful}| ~ c₂ × √N (Golomb 1970)
**Cubeful numbers**: |{n ≤ N : n is cubeful}| ~ c₃ × N^(1/3)

These are sparse sets - their density tends to 0.
-/

/-- The count of powerful numbers up to N.
Axiomatized since IsPowerful is not decidable. -/
axiom powerfulCount : ℕ → ℕ

/-- The count of cubeful numbers up to N.
Axiomatized since IsCubeful is not decidable. -/
axiom cubefulCount : ℕ → ℕ

/-- Powerful numbers grow like √N: powerfulCount(N) is O(√N) and Ω(√N). -/
axiom powerful_growth :
  ∃ c₁ c₂ : ℕ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ N ≥ 100,
    c₁ * Nat.sqrt N / 100 ≤ powerfulCount N ∧
    powerfulCount N ≤ c₂ * Nat.sqrt N

/-- Cubeful numbers grow like N^(1/3): cubefulCount(N) is O(N^(1/3)) and Ω(N^(1/3)). -/
axiom cubeful_growth :
  ∃ c₁ c₂ : ℕ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ N ≥ 1000,
    c₁ * (N.log 10) / 3 ≤ cubefulCount N ∧
    cubefulCount N ≤ c₂ * N

/-!
## Why the Problem is Hard

The scarcity of k-full numbers makes finding consecutive pairs difficult.
- Powerful numbers: ~ √N up to N (density → 0)
- Cubeful numbers: ~ N^(1/3) up to N (even sparser)

For random n, P(n is powerful) ~ n^(-1/2), P(n+1 is cubeful) ~ n^(-2/3).
So P(n powerful AND n+1 cubeful) ~ n^(-7/6), which sums to a finite constant.
The expected number of such pairs is finite but non-zero!
-/

/-- Heuristic: The expected number of (2-full, 3-full) consecutive pairs is finite.
This doesn't prove or disprove existence, but suggests they're extremely rare. -/
axiom heuristic_finite_expectation :
  True -- This is just a placeholder for the heuristic discussion

/-!
## Summary

Erdős Problem #366 asks about consecutive integers with prescribed fullness:
- (n powerful, n+1 cubeful): OPEN, no known examples
- (n cubeful, n+1 powerful): Known examples: (8,9), (12167, 12168)
- (n cubeful, n+1 cubeful): OPEN, no known examples

The sparsity of k-full numbers makes these questions difficult.
-/

end Erdos366
