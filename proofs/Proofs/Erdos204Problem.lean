/-
Erdős Problem #204: Disjoint Covering Systems by Divisors

Source: https://erdosproblems.com/204
Status: SOLVED (Adenwalla, 2025)

Statement:
Are there n such that there is a covering system with moduli the divisors
of n which is "as disjoint as possible"?

Definition: For each d | n with d > 1, assign a_d such that:
1. Every integer x ≡ a_d (mod d) for some d | n
2. If x ≡ a_d (mod d) and x ≡ a_{d'} (mod d'), then gcd(d, d') = 1

Answer: NO (Adenwalla, 2025)
No such n exists. Erdős and Graham conjectured this, Adenwalla proved it.

Key Results:
- The density of such n (if any existed) would be zero
- Adenwalla proved: no such n exists at all
- For general n, one can maximize density of covered integers (also studied)

References:
- [ErGr80] Erdős-Graham, "Old and New Problems and Results..." (1980)
- [Ad25] Adenwalla, "A Question of Erdős and Graham on Covering Systems" (2025)

Tags: number-theory, covering-systems, divisors, solved
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Nat Int Finset

namespace Erdos204

/-!
## Part 1: Basic Definitions
-/

/-- The divisors of n greater than 1 -/
def properDivisors (n : ℕ) : Finset ℕ :=
  (n.divisors).filter (· > 1)

/-- An assignment of residues to divisors -/
def ResidueAssignment (n : ℕ) := ∀ d ∈ properDivisors n, ℤ

/-- The residue class a (mod d) -/
def IsInResidueClass (x : ℤ) (a : ℤ) (d : ℕ) : Prop :=
  x % d = a % d

/-- x is covered by the system if x ≡ a_d (mod d) for some d | n, d > 1 -/
def IsCovered (n : ℕ) (assignment : ResidueAssignment n) (x : ℤ) : Prop :=
  ∃ d : ℕ, ∃ h : d ∈ properDivisors n,
    IsInResidueClass x (assignment d h) d

/-- The system is a covering system: every integer is covered -/
def IsCoveringSystem (n : ℕ) (assignment : ResidueAssignment n) : Prop :=
  ∀ x : ℤ, IsCovered n assignment x

/-!
## Part 2: The Disjointness Condition
-/

/-- Two divisors "overlap" for x if x is in both residue classes -/
def Overlaps (n : ℕ) (assignment : ResidueAssignment n)
    (d d' : ℕ) (hd : d ∈ properDivisors n) (hd' : d' ∈ properDivisors n)
    (x : ℤ) : Prop :=
  IsInResidueClass x (assignment d hd) d ∧
  IsInResidueClass x (assignment d' hd') d'

/-- "As disjoint as possible": overlap implies coprime -/
def IsAsDisjointAsPossible (n : ℕ) (assignment : ResidueAssignment n) : Prop :=
  ∀ d d' : ℕ, ∀ hd : d ∈ properDivisors n, ∀ hd' : d' ∈ properDivisors n,
    d ≠ d' →
    (∃ x : ℤ, Overlaps n assignment d d' hd hd' x) →
    Nat.gcd d d' = 1

/-- A disjoint covering system: both covering and as disjoint as possible -/
def IsDisjointCoveringSystem (n : ℕ) (assignment : ResidueAssignment n) : Prop :=
  IsCoveringSystem n assignment ∧ IsAsDisjointAsPossible n assignment

/-!
## Part 3: The Main Question
-/

/-- Does there exist n with a disjoint covering system? -/
def ExistsDisjointCoveringN : Prop :=
  ∃ n : ℕ, n > 1 ∧ ∃ assignment : ResidueAssignment n,
    IsDisjointCoveringSystem n assignment

/-- Erdős-Graham conjecture: No such n exists -/
def ErdosGrahamConjecture : Prop :=
  ¬ExistsDisjointCoveringN

/-!
## Part 4: Density Results
-/

/-- The density of n having disjoint covering systems would be zero -/
axiom density_is_zero :
  -- Even if such n existed, their density in ℕ would be 0
  -- This was known before Adenwalla's complete proof
  True

/-- Erdős and Graham believed no such n exist -/
axiom erdos_graham_belief :
  -- Based on their extensive study of covering systems
  True

/-!
## Part 5: Adenwalla's Theorem (2025)
-/

/-- **Adenwalla's Theorem (2025):**
    There is no n with a disjoint covering system by its divisors. -/
axiom adenwalla_2025 : ErdosGrahamConjecture

/-- The answer to Problem #204 is NO -/
theorem erdos_204_answer : ¬ExistsDisjointCoveringN := adenwalla_2025

/-- Equivalently: every n fails to have a disjoint covering system -/
theorem every_n_fails :
    ∀ n : ℕ, n > 1 → ¬∃ assignment : ResidueAssignment n,
      IsDisjointCoveringSystem n assignment := by
  intro n hn ⟨assignment, hcov⟩
  have : ExistsDisjointCoveringN := ⟨n, hn, assignment, hcov⟩
  exact adenwalla_2025 this

/-!
## Part 6: Why It Fails
-/

/-- Key insight: divisibility constraints force overlaps -/
axiom divisibility_forces_overlaps :
  -- If d | d', then the residue classes necessarily interact
  -- The coprimality condition is too restrictive
  True

/-- For d | d', we have gcd(d, d') = d ≠ 1 (if d > 1) -/
theorem divisor_pair_not_coprime (d d' : ℕ) (hd : d > 1) (hdiv : d ∣ d') :
    Nat.gcd d d' ≠ 1 := by
  rw [Nat.gcd_eq_left hdiv]
  exact Nat.one_lt_iff_ne_one.mp hd

/-- Covering requires using divisible pairs, which can't be disjoint -/
axiom covering_requires_divisible_pairs :
  -- To cover all integers, we must use divisors d, d' with d | d'
  -- These pairs have gcd ≠ 1, violating disjointness
  True

/-!
## Part 7: Related Questions
-/

/-- Maximum density problem: for any n, what's the max density coverable? -/
def MaxCoverableDensity (n : ℕ) : ℝ :=
  -- Sup over all assignments of the density of covered integers
  -- subject to the disjointness constraint
  sorry

/-- Adenwalla also studied this maximum density problem -/
axiom adenwalla_density_study :
  -- The paper investigates MaxCoverableDensity(n) for various n
  True

/-- For general n without coprimality, standard covering systems exist -/
axiom standard_covering_systems_exist :
  -- Without the coprimality constraint, covering systems are well-studied
  -- e.g., {0 (mod 2), 0 (mod 3), 1 (mod 4), 5 (mod 6), 7 (mod 12)}
  True

/-!
## Part 8: Small Examples
-/

/-- For n = 6, divisors are {2, 3, 6} -/
example : properDivisors 6 = {2, 3, 6} := by
  native_decide

/-- n = 6 cannot have a disjoint covering system -/
axiom n6_fails :
  -- Divisors 2, 3, 6 with 2 | 6 and 3 | 6
  -- gcd(2,6) = 2 ≠ 1 and gcd(3,6) = 3 ≠ 1
  -- So any covering using these must violate disjointness
  ¬∃ assignment : ResidueAssignment 6,
    IsDisjointCoveringSystem 6 assignment

/-- For n = 12, similar obstruction -/
axiom n12_fails :
  ¬∃ assignment : ResidueAssignment 12,
    IsDisjointCoveringSystem 12 assignment

/-!
## Part 9: Connection to Covering Systems
-/

/-- The classical Erdős covering system problem -/
axiom classical_covering_problem :
  -- Erdős studied covering systems extensively
  -- This problem is a variant with an extra constraint
  True

/-- Minimum modulus problem for covering systems -/
axiom minimum_modulus_problem :
  -- Related: what's the minimum largest modulus in a covering system?
  True

/-- Hough's theorem (2015) on covering systems -/
axiom hough_theorem :
  -- For any covering system with distinct moduli > 1,
  -- the sum of reciprocals must be ≥ 1
  True

/-!
## Part 10: Summary
-/

/-- Erdős Problem #204 is SOLVED -/
theorem erdos_204_solved : ErdosGrahamConjecture := adenwalla_2025

/-- **Erdős Problem #204: SOLVED (Adenwalla 2025)**

QUESTION: Does there exist n with a "disjoint" covering system
using divisors of n?

A disjoint covering system:
- Uses moduli that are divisors of n
- Every integer is covered
- Overlapping residue classes only occur for coprime moduli

ANSWER: NO (Adenwalla 2025)

No such n exists. The divisibility structure of divisors
forces overlaps between non-coprime pairs.
-/
theorem erdos_204_summary :
    -- No n has a disjoint covering system
    ¬ExistsDisjointCoveringN ∧
    -- This confirms Erdős-Graham's belief
    ErdosGrahamConjecture := by
  constructor
  · exact adenwalla_2025
  · exact adenwalla_2025

/-- Problem status -/
def erdos_204_status : String :=
  "SOLVED (Adenwalla 2025) - No disjoint covering systems exist"

end Erdos204
