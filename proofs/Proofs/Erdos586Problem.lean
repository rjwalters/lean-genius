/-
  Erdős Problem #586: Covering Systems with Antichain Moduli

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

/-! ## Basic Definitions -/

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

/-! ## Covering Systems -/

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

/-! ## Antichain Condition -/

/-- Two natural numbers are comparable under divisibility -/
def Divides (a b : ℕ) : Prop := a ∣ b ∨ b ∣ a

/-- A set of moduli forms an antichain if no two divide each other -/
def IsAntichain (M : Finset ℕ) : Prop :=
  ∀ a ∈ M, ∀ b ∈ M, a ≠ b → ¬(a ∣ b) ∧ ¬(b ∣ a)

/-- A covering system has antichain moduli if no modulus divides another -/
def HasAntichainModuli (S : CoveringSystem) : Prop :=
  IsAntichain S.moduli

/-! ## The Main Question -/

/-- Does there exist a covering system with antichain moduli? -/
def schinzel_question : Prop :=
  ∃ S : CoveringSystem, IsCovering S ∧ HasAntichainModuli S

/-! ## The Main Result -/

/-- Balister-Bollobás-Morris-Sahasrabudhe-Tiba (2022):
    There is NO covering system with antichain moduli -/
theorem bbmst_theorem : ¬schinzel_question := by
  sorry -- [BBMST22]

/-- Equivalent formulation: every covering system has comparable moduli -/
theorem covering_implies_comparable :
    ∀ S : CoveringSystem, IsCovering S →
    ∃ a ∈ S.moduli, ∃ b ∈ S.moduli, a ≠ b ∧ (a ∣ b ∨ b ∣ a) := by
  sorry -- Consequence of bbmst_theorem

/-! ## Related: Classical Covering Systems -/

/-- Example: The simplest covering system {0 (mod 2), 1 (mod 2)} -/
def trivialCovering : CoveringSystem where
  classes := {
    ⟨0, 2, by norm_num⟩,
    ⟨1, 2, by norm_num⟩
  }
  nonempty := by simp

theorem trivial_is_covering : IsCovering trivialCovering := by
  sorry

/-- Example: A non-trivial covering system
    0 (mod 2), 0 (mod 3), 1 (mod 4), 5 (mod 6), 7 (mod 12)
    This has moduli {2, 3, 4, 6, 12} which are NOT an antichain -/
def erdos_covering : CoveringSystem where
  classes := {
    ⟨0, 2, by norm_num⟩,
    ⟨0, 3, by norm_num⟩,
    ⟨1, 4, by norm_num⟩,
    ⟨5, 6, by norm_num⟩,
    ⟨7, 12, by norm_num⟩
  }
  nonempty := by simp

theorem erdos_covering_is_covering : IsCovering erdos_covering := by
  sorry

theorem erdos_covering_not_antichain : ¬HasAntichainModuli erdos_covering := by
  sorry -- 2 | 4, 2 | 6, 2 | 12, 3 | 6, 3 | 12, 4 | 12, 6 | 12

/-! ## Minimum Modulus Problem -/

/-- The minimum modulus in a covering system -/
def minModulus (S : CoveringSystem) : ℕ :=
  S.moduli.min' (by
    simp [CoveringSystem.moduli]
    exact ⟨_, S.classes.min'_mem S.nonempty, rfl⟩)

/-- Erdős's conjecture: The minimum modulus in any covering system
    with distinct odd moduli > 1 can be arbitrarily large.
    This is related but distinct from the antichain question. -/
def erdos_minimum_modulus_conjecture : Prop :=
  ∀ N : ℕ, ∃ S : CoveringSystem,
    IsCovering S ∧
    (∀ n ∈ S.moduli, n > 1 ∧ Odd n) ∧
    S.moduli.card = S.classes.card ∧  -- distinct moduli
    minModulus S > N

/-! ## Density Results -/

/-- The density of uncovered integers when moduli are bounded -/
noncomputable def uncoveredDensity (S : CoveringSystem) : ℝ :=
  1 - (S.classes.sum fun c => 1 / (c.modulus : ℝ))

/-- BBMST key lemma: Density bound for antichain moduli -/
theorem bbmst_density_bound :
    ∀ S : CoveringSystem, HasAntichainModuli S →
    uncoveredDensity S > 0 := by
  sorry -- Key technical result in [BBMST22]

/-- Corollary: Antichain moduli cannot cover all integers -/
theorem antichain_not_covering :
    ∀ S : CoveringSystem, HasAntichainModuli S → ¬IsCovering S := by
  intro S hAnti
  intro hCov
  have hDens := bbmst_density_bound S hAnti
  -- If density > 0, then some integers are uncovered, contradiction
  sorry

/-! ## The Proof Strategy -/

/-- The BBMST proof uses probabilistic and analytic methods to show
    that any collection with antichain moduli must leave positive
    density of integers uncovered. -/
theorem bbmst_strategy :
    -- 1. Define a measure on uncovered integers
    -- 2. Show antichain condition limits coverage
    -- 3. Use sieving inequalities to bound uncovered density from below
    -- 4. Positive density implies not all integers covered
    True := trivial

/-! ## Related Problems -/

/-- Related: Erdős-Selfridge problem on covering systems [Problem 7] -/
def erdos_selfridge_related : Prop :=
  -- Can you find a covering system where all moduli are odd?
  ∃ S : CoveringSystem, IsCovering S ∧ ∀ n ∈ S.moduli, Odd n

/-- This remains open! Unlike the antichain question, odd moduli
    covering systems are not ruled out. -/
theorem erdos_selfridge_open : True := trivial

/-! ## Generalizations -/

/-- A k-covering: every integer is covered by at least k classes -/
def IsKCovering (S : CoveringSystem) (k : ℕ) : Prop :=
  ∀ x : ℤ, (S.classes.filter fun c => x ∈ c.toSet).card ≥ k

/-- Question: What about k-coverings with antichain moduli? -/
def antichain_k_covering_question (k : ℕ) : Prop :=
  ∃ S : CoveringSystem, IsKCovering S k ∧ HasAntichainModuli S

/-- BBMST implies no k-covering with antichain moduli for any k ≥ 1 -/
theorem no_antichain_k_covering (k : ℕ) (hk : k ≥ 1) :
    ¬antichain_k_covering_question k := by
  sorry -- Follows from density argument

/-! ## Summary

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

end Erdos586
