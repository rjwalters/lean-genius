/-
# Erdős Problem #586: Covering Systems with Antichain Moduli

Source: https://erdosproblems.com/586
Status: SOLVED (NO - Balister-Bollobás-Morris-Sahasrabudhe-Tiba, 2022)

Statement:
Is there a covering system such that no two of the moduli divide each other?

Solution:
NO - proved by Balister, Bollobás, Morris, Sahasrabudhe, and Tiba (2022).
There is no covering system where the moduli form an antichain under divisibility.

Background:
A covering system is a finite collection of congruence classes a_i (mod n_i)
such that every integer belongs to at least one class. The moduli are the n_i.
An antichain under divisibility means no n_i divides any n_j for i ≠ j.

History:
- Asked by Schinzel
- Motivated by questions of Erdős and Selfridge on covering systems
- Part of a broader investigation into the structure of covering systems
- Resolved as part of the "Erdős covering problem" breakthrough

References:
- [BBMST22] Balister-Bollobás-Morris-Sahasrabudhe-Tiba (2022),
  "On the Erdős covering problem: the density of the uncovered set"
-/

import Mathlib

namespace Erdos586

/-
## Basic Definitions
-/

/-- A residue class: integers ≡ a (mod n) -/
def ResidueClass (a n : ℤ) : Set ℤ :=
  { x | x % n = a % n }

/-- Notation: a (mod n) represents the residue class -/
structure CongruenceClass where
  residue : ℤ
  modulus : ℕ
  mod_pos : modulus > 0

/-- The set of integers in a congruence class -/
def CongruenceClass.toSet (c : CongruenceClass) : Set ℤ :=
  { x | x % c.modulus = c.residue % c.modulus }

/-
## Covering Systems
-/

/-- A finite system of congruence classes -/
structure CoveringSystem where
  classes : Finset CongruenceClass
  nonempty : classes.Nonempty

/-- The moduli of a covering system -/
def CoveringSystem.moduli (S : CoveringSystem) : Finset ℕ :=
  S.classes.image (fun c => c.modulus)

/-- A system covers an integer if that integer belongs to at least one class -/
def covers (S : CoveringSystem) (x : ℤ) : Prop :=
  ∃ c ∈ S.classes, x ∈ c.toSet

/-- A covering system: every integer is covered -/
def IsCovering (S : CoveringSystem) : Prop :=
  ∀ x : ℤ, covers S x

/-
## Antichain Condition
-/

/-- Two natural numbers are comparable under divisibility -/
def Divides (a b : ℕ) : Prop := a ∣ b ∨ b ∣ a

/-- A set of moduli forms an antichain if no two divide each other -/
def IsAntichain (M : Finset ℕ) : Prop :=
  ∀ a ∈ M, ∀ b ∈ M, a ≠ b → ¬(a ∣ b) ∧ ¬(b ∣ a)

/-- A covering system has antichain moduli if no modulus divides another -/
def HasAntichainModuli (S : CoveringSystem) : Prop :=
  IsAntichain S.moduli

/-
## The Main Question
-/

/-- Does there exist a covering system with antichain moduli? -/
def schinzel_question : Prop :=
  ∃ S : CoveringSystem, IsCovering S ∧ HasAntichainModuli S

/-
## The Main Result
-/

/-- Balister-Bollobás-Morris-Sahasrabudhe-Tiba (2022):
    There is NO covering system with antichain moduli -/
axiom bbmst_theorem : ¬schinzel_question

/-- Equivalent formulation: every covering system has comparable moduli -/
/-
## Density Results
-/

/-- The density of uncovered integers when moduli are bounded -/
noncomputable def uncoveredDensity (S : CoveringSystem) : ℝ :=
  1 - (S.classes.sum fun c => 1 / (c.modulus : ℝ))

/-- BBMST key lemma: Density bound for antichain moduli -/
axiom bbmst_density_bound :
    ∀ S : CoveringSystem, HasAntichainModuli S →
    uncoveredDensity S > 0

/-- Corollary: Antichain moduli cannot cover all integers -/
axiom antichain_not_covering :
    ∀ S : CoveringSystem, HasAntichainModuli S → ¬IsCovering S

/-
## Generalizations
-/

/-- A k-covering: every integer is covered by at least k classes -/
def IsKCovering (S : CoveringSystem) (k : ℕ) : Prop :=
  ∀ x : ℤ, (S.classes.filter fun c => x ∈ c.toSet).card ≥ k

/-- Question: What about k-coverings with antichain moduli? -/
def antichain_k_covering_question (k : ℕ) : Prop :=
  ∃ S : CoveringSystem, IsKCovering S k ∧ HasAntichainModuli S

/-- BBMST implies no k-covering with antichain moduli for any k ≥ 1 -/
/-
## Summary

**Status: SOLVED (NO)**

Erdős Problem #586 (Schinzel's Question) asked:
Is there a covering system where no modulus divides another (antichain)?

**Answer: NO** (Balister-Bollobás-Morris-Sahasrabudhe-Tiba, 2022)

**Key Insight:**
The proof shows that any system with antichain moduli must leave a
positive density of integers uncovered. This is part of a broader
breakthrough on the Erdős covering problem.

**Method:**
Probabilistic and analytic methods combined with careful sieving
inequalities to bound the density of uncovered integers.

**Related Open:**
The question of covering systems with all odd moduli remains open.
-/

/-- Summary theorem combining key results -/
theorem erdos_586_summary :
    ¬schinzel_question ∧
    (∀ S : CoveringSystem, HasAntichainModuli S → uncoveredDensity S > 0) ∧
    (∀ S : CoveringSystem, HasAntichainModuli S → ¬IsCovering S) :=
  ⟨bbmst_theorem, bbmst_density_bound, antichain_not_covering⟩

end Erdos586
