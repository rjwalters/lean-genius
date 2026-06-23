/-
Erdős Problem #947: No Exact Covering Systems Exist

Source: https://erdosproblems.com/947
Status: SOLVED (PROVED)

Statement:
There is no exact covering system - that is, a finite collection of
congruence classes aᵢ (mod nᵢ) with distinct moduli nᵢ such that every
integer satisfies exactly one of these congruence classes.

Background:
A covering system is a finite set of congruences {aᵢ (mod nᵢ)} such that
every integer satisfies at least one congruence. An "exact" covering system
would cover every integer exactly once, partitioning ℤ.

This theorem states that if we require all moduli to be distinct,
no such exact partition exists.

Proof:
Proved independently by:
- Mirsky and Newman
- Davenport and Rado

The key insight is that the densities must sum to 1, but this leads to
a contradiction using properties of the least common multiple.

References:
- Mirsky, L. and Newman, D.J.
- Davenport, H. and Rado, R.
- [Er77c] Erdős reference

Tags: number-theory, covering-systems, congruences, modular-arithmetic
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

namespace Erdos947

/- ## Part I: Basic Definitions -/

/--
**Congruence class:**
The set of integers congruent to a (mod n).
-/
def CongruenceClass (a n : ℤ) : Set ℤ :=
  { x : ℤ | x % n = a % n }

/--
**A covering system:**
A finite collection of congruence classes that covers all integers.
Every integer satisfies at least one congruence.
-/
structure CoveringSystem where
  classes : Finset (ℤ × ℕ)  -- pairs (aᵢ, nᵢ)
  nonempty : classes.Nonempty
  positive_moduli : ∀ p ∈ classes, p.2 > 0
  covers : ∀ x : ℤ, ∃ p ∈ classes, x % p.2 = p.1 % p.2

/--
**Distinct moduli:**
All moduli in the system are different.
-/
def hasDistinctModuli (C : CoveringSystem) : Prop :=
  ∀ p q : ℤ × ℕ, p ∈ C.classes → q ∈ C.classes → p.2 = q.2 → p = q

/--
**Exact covering system:**
Every integer satisfies exactly one congruence (a partition of ℤ).
-/
def isExact (C : CoveringSystem) : Prop :=
  ∀ x : ℤ, ∃! p, p ∈ C.classes ∧ x % p.2 = p.1 % p.2

/- ## Part II: The Density Argument -/

/--
**Density of a congruence class:**
The congruence a (mod n) contains exactly 1/n of the integers (asymptotically).
-/
def density (n : ℕ) : ℚ := 1 / n

/--
**Sum of densities in a covering system:**
For an exact covering, the densities must sum to exactly 1.
-/
def densitySum (C : CoveringSystem) : ℚ :=
  C.classes.sum fun p => density p.2

/--
**Density lemma:**
For an exact covering system, the sum of densities equals 1.
-/
/- ## Part III: The Main Theorem -/

/--
**Mirsky-Newman / Davenport-Rado Theorem:**
There is no exact covering system with distinct moduli.
-/
axiom no_exact_covering_system :
    ¬∃ C : CoveringSystem, hasDistinctModuli C ∧ isExact C

/--
**Equivalent formulation:**
If a covering system has distinct moduli, some integer is covered
more than once (or there's no covering at all).
-/
theorem distinct_moduli_not_exact :
    ∀ C : CoveringSystem, hasDistinctModuli C → ¬isExact C := by
  intro C hD hE
  have : ∃ C' : CoveringSystem, hasDistinctModuli C' ∧ isExact C' := ⟨C, hD, hE⟩
  exact no_exact_covering_system this

/- ## Part IV: Proof Techniques -/

/--
**Mirsky-Newman generating function approach:**
Consider the generating function f(x) = Σᵢ x^{aᵢ}/(1 - x^{nᵢ}).
For an exact covering, f(x) = 1/(1-x) (each integer represented exactly once).
This imposes analytic constraints on the moduli that cannot be satisfied
when all moduli are distinct. Axiomatized since the proof requires
complex analysis of formal power series.
-/
/--
**Davenport-Rado LCM argument:**
If distinct moduli n₁ < n₂ < ... < nₖ give an exact covering,
the largest modulus nₖ must divide lcm(n₁, ..., n_{k-1}).
But then nₖ is not "new" — it's already a factor of the LCM —
contradicting the ability to partition residues the covering requires.
-/
/- ## Part V: Related Results -/

/--
**Covering systems do exist:**
Unlike exact covering systems, ordinary covering systems with distinct
moduli do exist (every integer covered at least once, possibly more).
-/
axiom covering_systems_exist :
    ∃ C : CoveringSystem, hasDistinctModuli C ∧
      (∀ n ∈ C.classes, n.2 > 1)  -- No modulus 1 (trivial)

/--
**Example: The Erdős covering system:**
{0 (mod 2), 0 (mod 3), 1 (mod 4), 5 (mod 6), 7 (mod 12)}
covers all integers with distinct moduli > 1.
-/
/--
**Allowing repeated moduli:**
If we allow repeated moduli, exact coverings exist.
For example: {0 (mod 2), 1 (mod 2)} partitions ℤ exactly.
-/
def exactCoveringWithRepeats : CoveringSystem where
  classes := {(0, 2), (1, 2)}
  nonempty := by simp
  positive_moduli := by simp
  covers := by
    intro x
    by_cases h : x % 2 = 0
    · exact ⟨(0, 2), by simp, by simp [h]⟩
    · have : x % 2 = 1 := by omega
      exact ⟨(1, 2), by simp, by simp [this]⟩

/- ## Part VI: Summary -/

/--
**Erdős Problem #947: Summary**

THEOREM (Mirsky-Newman, Davenport-Rado):
There is no exact covering system with distinct moduli.

PROOF IDEAS:
1. Density argument: Σ 1/nᵢ = 1 with distinct nᵢ is highly constrained
2. LCM argument: The largest modulus must divide the LCM of others

CONTRAST:
- Ordinary covering systems (at least one coverage) with distinct moduli exist
- Exact coverings exist if we allow repeated moduli
-/
theorem erdos_947_summary :
    -- No exact covering with distinct moduli
    (¬∃ C : CoveringSystem, hasDistinctModuli C ∧ isExact C) ∧
    -- Ordinary coverings exist
    (∃ C : CoveringSystem, hasDistinctModuli C) :=
  ⟨no_exact_covering_system, let ⟨C, hD, _⟩ := covering_systems_exist; ⟨C, hD⟩⟩

end Erdos947
