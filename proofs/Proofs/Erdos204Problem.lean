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

import Mathlib

open Nat Int Finset

namespace Erdos204

/-
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

/-
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

/-
## Part 3: The Main Question
-/

/-- Does there exist n with a disjoint covering system? -/
def ExistsDisjointCoveringN : Prop :=
  ∃ n : ℕ, n > 1 ∧ ∃ assignment : ResidueAssignment n,
    IsDisjointCoveringSystem n assignment

/-- Erdős-Graham conjecture: No such n exists -/
def ErdosGrahamConjecture : Prop :=
  ¬ExistsDisjointCoveringN

/-
## Part 4: Density Results
-/

/-
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

/-
## Part 6: Why It Fails
-/

/-- For d | d', we have gcd(d, d') = d ≠ 1 (if d > 1) -/
theorem divisor_pair_not_coprime (d d' : ℕ) (hd : d > 1) (hdiv : d ∣ d') :
    Nat.gcd d d' ≠ 1 := by
  rw [Nat.gcd_eq_left hdiv]
  exact hd.ne'

/-
## Part 7: Related Questions
-/

/-- Maximum density coverable: upper bound via union bound.
    For each divisor d > 1 of n, a residue class mod d covers 1/d of integers.
    This sum is an upper bound on the density of the union. -/
noncomputable def MaxCoverableDensity (n : ℕ) : ℝ :=
  ∑ d ∈ properDivisors n, (1 : ℝ) / (d : ℝ)

/-
## Part 8: Small Examples
-/

/-- For n = 6, divisors are {2, 3, 6} -/
example : properDivisors 6 = {2, 3, 6} := by
  native_decide

/-
## Part 9: Connection to Covering Systems
-/

/-
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
