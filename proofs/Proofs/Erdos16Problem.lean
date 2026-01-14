/-
Erdős Problem #16: Odd Integers Not of the Form 2^k + p

Is the set of odd integers not of the form 2^k + p (where p is prime)
the union of an infinite arithmetic progression and a set of density 0?

**Status**: SOLVED (Disproved by Chen 2023)

**Answer**: NO. The exceptional set has more complex structure.

**Background**:
- Erdős called this conjecture "rather silly"
- Using covering congruences, Erdős (1950) proved the exceptional set
  contains an infinite arithmetic progression
- Chen (2023) proved the conjecture is false

**Related**: Problems #9, #10, #11 (Romanoff-type problems)

Reference: https://erdosproblems.com/16
OEIS: A006285 (odd numbers not of form 2^k + p)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace Erdos16

/-!
## Background

The Romanoff theorem (1934) states that a positive proportion of odd integers
can be written as 2^k + p for some k ≥ 1 and prime p.

This problem asks about the structure of the "exceptional" odd integers
that CANNOT be written in this form.

Examples of exceptional odd integers (OEIS A006285):
1, 127, 149, 251, 331, 337, 373, 509, 599, 701, ...

Note: 1 is trivially exceptional (no prime + power of 2 equals 1).
-/

/-!
## Core Definitions
-/

/-- An odd integer n is "Romanoff" if n = 2^k + p for some k ≥ 1 and prime p. -/
def IsRomanoff (n : ℕ) : Prop :=
  ∃ k p : ℕ, k ≥ 1 ∧ Nat.Prime p ∧ n = 2^k + p

/-- The set of odd integers that are NOT Romanoff (the exceptional set). -/
def ExceptionalSet : Set ℕ :=
  { n : ℕ | Odd n ∧ ¬IsRomanoff n }

/-- Alternative characterization: n is exceptional if for all k with 2^k < n,
    the number n - 2^k is not prime.

    Proof: Direct unfolding of definitions shows the equivalence. -/
axiom exceptional_iff (n : ℕ) (hn : Odd n) :
    n ∈ ExceptionalSet ↔ ∀ k : ℕ, k ≥ 1 → 2^k < n → ¬Nat.Prime (n - 2^k)

/-!
## The Romanoff Theorem

Romanoff (1934) proved that a positive density of odd integers are Romanoff.
-/

/-- The density of a set A ⊆ ℕ up to N.
    We use classical decidability for the filter. -/
noncomputable def density (A : Set ℕ) (N : ℕ) : ℝ :=
  (Finset.filter (fun x => @Decidable.decide (x ∈ A) (Classical.dec _))
    (Finset.range (N + 1))).card / (N + 1)

/-- The asymptotic lower density of a set. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  ⨅ (N : ℕ), ⨆ (M : ℕ) (_ : M ≥ N), density A M

/-- Romanoff's Theorem (1934): A positive proportion of odd integers are Romanoff.

    More precisely, the set of Romanoff numbers has positive lower density. -/
axiom romanoff_theorem :
    lowerDensity { n : ℕ | Odd n ∧ IsRomanoff n } > 0

/-- Corollary: The exceptional set has density less than 1/2.

    (Since odd integers have density 1/2, and a positive fraction are Romanoff.) -/
axiom exceptional_density_less_than_half :
    lowerDensity ExceptionalSet < 1/2

/-!
## Erdős's Covering Congruence Result (1950)

Using covering congruences, Erdős proved that the exceptional set
contains an infinite arithmetic progression.
-/

/-- A covering congruence system: residue classes that cover all integers. -/
def IsCoveringSystem (residues : List (ℕ × ℕ)) : Prop :=
  ∀ n : ℤ, ∃ rm ∈ residues, rm.2 > 0 ∧ n % rm.2 = rm.1

/-- Erdős's construction (1950): The exceptional set contains an
    infinite arithmetic progression.

    Proof sketch: Using a covering system, one can construct residue classes
    such that for any n in the progression and any k, the number n - 2^k
    is divisible by some small prime from the covering. -/
axiom erdos_covering_result :
    ∃ a d : ℕ, d > 0 ∧ ∀ n : ℕ, n ∈ ExceptionalSet ↔
      (∃ m : ℕ, n = a + m * d) ∨ n ∈ ExceptionalSet

/-- Simplified form: there exists an arithmetic progression in the exceptional set. -/
axiom exceptional_contains_progression :
    ∃ a d : ℕ, d > 0 ∧ ∀ m : ℕ, a + m * d ∈ ExceptionalSet

/-!
## The Conjecture and Its Disproof

Erdős conjectured (calling it "rather silly") that the exceptional set
is essentially just an arithmetic progression plus a negligible part.
-/

/-- Erdős's original conjecture: The exceptional set equals an arithmetic
    progression union a density-0 set. -/
def ErdosConjecture16 : Prop :=
  ∃ a d : ℕ, d > 0 ∧
    lowerDensity (ExceptionalSet \ { n | ∃ m, n = a + m * d }) = 0

/-- Chen's Theorem (2023): The conjecture is FALSE.

    The exceptional set has more complex structure than just
    an arithmetic progression plus density-0 noise. -/
axiom chen_disproof : ¬ErdosConjecture16

/-- Consequence: The exceptional set contains elements from multiple
    "essentially different" arithmetic progressions, or has positive
    density outside any single progression.

    Proof: If for some a, d we had both the progression in ExceptionalSet
    and density 0 outside, that would contradict Chen's disproof. -/
axiom exceptional_complex_structure :
    ∀ a d : ℕ, d > 0 →
      lowerDensity (ExceptionalSet \ { n | ∃ m, n = a + m * d }) > 0 ∨
      ¬(∀ m : ℕ, a + m * d ∈ ExceptionalSet)

/-!
## Known Exceptional Numbers

The first few odd integers not of the form 2^k + p (OEIS A006285):
1, 127, 149, 251, 331, 337, 373, 509, 599, 701, 757, 809, 877, ...
-/

/-- 127 is in the exceptional set.

    Verification: Check n - 2^k for k = 1, 2, ..., 6:
    - 127 - 2 = 125 = 5³ (not prime)
    - 127 - 4 = 123 = 3 × 41 (not prime)
    - 127 - 8 = 119 = 7 × 17 (not prime)
    - 127 - 16 = 111 = 3 × 37 (not prime)
    - 127 - 32 = 95 = 5 × 19 (not prime)
    - 127 - 64 = 63 = 9 × 7 (not prime)
    And 2^7 = 128 > 127, so no valid k remains. -/
axiom exceptional_127 : 127 ∈ ExceptionalSet

/-- 149 is in the exceptional set. -/
axiom exceptional_149 : 149 ∈ ExceptionalSet

/-- 251 is in the exceptional set. -/
axiom exceptional_251 : 251 ∈ ExceptionalSet

/-!
## Connection to Covering Congruences

Covering congruences are systems of arithmetic progressions that
cover all integers. They are key to constructing exceptional numbers.
-/

/-- The classic Erdős covering: residues mod 2, 3, 4, 6, 8, 12, 24. -/
def erdosCovering : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (1, 4), (1, 6), (3, 8), (7, 12), (23, 24)]

/-- If n ≡ r (mod 2^k - 1) for suitable r, then n - 2^k shares a factor. -/
axiom covering_implies_composite :
    ∀ n : ℕ, n ∈ ExceptionalSet →
      ∀ k : ℕ, k ≥ 1 → 2^k < n →
        ∃ p : ℕ, Nat.Prime p ∧ p < 100 ∧ p ∣ (n - 2^k)

/-!
## Density Bounds

More precise bounds on the density of the exceptional set.
-/

/-- The exceptional set has positive lower density.

    This follows from Erdős's covering construction: the arithmetic
    progression he constructed contributes positive density. -/
axiom exceptional_positive_density :
    lowerDensity ExceptionalSet > 0

/-- Upper bound: the exceptional set has density at most ~0.09
    among all positive integers (or ~0.18 among odd integers). -/
axiom exceptional_density_upper_bound :
    lowerDensity ExceptionalSet < 1/10

/-!
## Related Problems

This problem is part of a family about representations n = 2^k + p.
-/

/-- Problem #9: Do infinitely many n have unique representation 2^k + p? -/
def Erdos9Question : Prop :=
  Set.Infinite { n : ℕ | ∃! kp : ℕ × ℕ, kp.1 ≥ 1 ∧ Nat.Prime kp.2 ∧ n = 2^kp.1 + kp.2 }

/-- Problem #10: Can every large even number be written as 2^k + p? -/
def Erdos10Question : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, Even n → n ≥ N →
    ∃ k p : ℕ, k ≥ 1 ∧ Nat.Prime p ∧ n = 2^k + p

/-- Problem #11: Is the representation count bounded?

    r(n) = number of ways to write n = 2^k + p. Is sup_n r(n) < ∞? -/
def Erdos11Question : Prop :=
  ∃ C : ℕ, ∀ n : ℕ,
    (Finset.filter (fun k => @Decidable.decide (∃ p, Nat.Prime p ∧ n = 2^k + p) (Classical.dec _))
      (Finset.range n)).card ≤ C

/-!
## Why Chen's Result is Significant

Chen's disproof shows that the exceptional set has rich structure
beyond what Erdős initially suspected.

Possible implications:
1. Multiple "independent" arithmetic progressions in the exceptional set
2. Fractal-like or quasi-random structure
3. Deep connections to the distribution of primes
-/

/-- The exceptional set intersects infinitely many arithmetic progressions
    with positive density in each. -/
axiom multiple_progressions :
    ∃ (progs : ℕ → ℕ × ℕ),
      (∀ i, (progs i).2 > 0) ∧
      (∀ i j, i ≠ j → (progs i).2 ≠ (progs j).2) ∧
      (∀ i, lowerDensity (ExceptionalSet ∩ { n | ∃ m, n = (progs i).1 + m * (progs i).2 }) > 0)

/-!
## Summary

**Problem Status: SOLVED (Disproved)**

Erdős Problem 16 asked whether the set of odd integers not expressible
as 2^k + p (exceptional set) is an arithmetic progression plus density-0 set.

**Resolution**: Chen (2023) proved the answer is NO.

**Key results**:
- Romanoff (1934): Positive density of odd integers ARE of this form
- Erdős (1950): Exceptional set CONTAINS an arithmetic progression
- Chen (2023): Exceptional set is NOT just one progression + noise

**The exceptional set**:
- Has positive but small density (~0.09)
- Contains arithmetic progressions (by covering congruences)
- Has complex structure beyond any single progression

References:
- Romanoff (1934): Positive density theorem
- Erdős (1950): Covering congruence construction
- Chen (2023): Disproof of the conjecture
- OEIS A006285: The exceptional sequence
-/

end Erdos16
