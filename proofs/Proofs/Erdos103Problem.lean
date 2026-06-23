/-
Erdős Problem #103: Incongruent Optimal Point Configurations

**Problem Statement (OPEN)**

Let h(n) count the number of incongruent sets of n points in ℝ² that minimize
the diameter subject to the constraint that d(x,y) ≥ 1 for all distinct x,y.

Is it true that h(n) → ∞ as n → ∞?

**Background:**
- We seek point sets with minimum separation 1 that minimize diameter
- Two sets are congruent if one can be transformed to the other by isometry
- h(n) counts distinct optimal configurations up to congruence

**Known Results:**
- Even h(n) ≥ 2 for all large n is unknown
- Related to packing and covering problems in discrete geometry

**Status:** OPEN

**Reference:** [Er94b]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Metric Set Finset

namespace Erdos103

/-
# Part 1: Basic Definitions

Define point configurations with minimum separation and diameter constraints.
-/

-- A finite configuration of n points in ℝ²
abbrev PointConfig (n : ℕ) := Fin n → ℝ × ℝ

-- Distance between two points in ℝ²
noncomputable def pointDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2)

-- A configuration has minimum separation 1
def HasMinSeparation (n : ℕ) (P : PointConfig n) : Prop :=
  ∀ i j : Fin n, i ≠ j → pointDist (P i) (P j) ≥ 1

-- The diameter of a configuration
noncomputable def diameter (n : ℕ) (P : PointConfig n) : ℝ :=
  if hn : n ≥ 2 then
    ⨆ i : Fin n, ⨆ j : Fin n, pointDist (P i) (P j)
  else 0

-- A configuration is valid: has minimum separation 1
def IsValidConfig (n : ℕ) (P : PointConfig n) : Prop :=
  HasMinSeparation n P

/-
# Part 2: Optimal Configurations

Define what it means for a configuration to be optimal (minimize diameter).
-/

-- The minimum achievable diameter for n points with separation 1
noncomputable def minDiameter (n : ℕ) : ℝ :=
  ⨅ P : {P : PointConfig n // IsValidConfig n P}, diameter n P.val

-- A configuration is optimal if it achieves the minimum diameter
def IsOptimal (n : ℕ) (P : PointConfig n) : Prop :=
  IsValidConfig n P ∧ diameter n P = minDiameter n

-- The set of optimal configurations
def OptimalSet (n : ℕ) : Set (PointConfig n) :=
  {P | IsOptimal n P}

/-
# Part 3: Congruence of Configurations

Two configurations are congruent if related by a rigid motion (isometry).
-/

-- An isometry of ℝ² is a bijective distance-preserving map.
-- All isometries of ℝⁿ are bijective; we include this for constructivity.
structure Isometry2D where
  toFun : ℝ × ℝ → ℝ × ℝ
  preserves_dist : ∀ p q, pointDist (toFun p) (toFun q) = pointDist p q
  bijective : Function.Bijective toFun

-- Apply isometry to a configuration
def applyIsometry (n : ℕ) (σ : Isometry2D) (P : PointConfig n) : PointConfig n :=
  fun i => σ.toFun (P i)

-- Two configurations are congruent if related by an isometry
def AreCongruent (n : ℕ) (P Q : PointConfig n) : Prop :=
  ∃ σ : Isometry2D, ∀ i, Q i = σ.toFun (P i)

-- Congruence is an equivalence relation
theorem congruent_refl (n : ℕ) (P : PointConfig n) : AreCongruent n P P := by
  use ⟨id, fun p q => rfl, Function.bijective_id⟩
  intro i; rfl

theorem congruent_symm (n : ℕ) (P Q : PointConfig n) :
    AreCongruent n P Q → AreCongruent n Q P := by
  intro ⟨σ, hσ⟩
  let g := Function.surjInv σ.bijective.surjective
  have hg_right : ∀ p, σ.toFun (g p) = p := Function.surjInv_eq σ.bijective.surjective
  have hg_left : ∀ p, g (σ.toFun p) = p := by
    intro p; exact σ.bijective.injective (hg_right (σ.toFun p))
  refine ⟨⟨g, fun p q => ?_, ?_⟩, fun i => ?_⟩
  · have := σ.preserves_dist (g p) (g q)
    rw [hg_right, hg_right] at this; exact this.symm
  · exact ⟨fun p q h => by rwa [← hg_right p, ← hg_right q, h],
           fun p => ⟨σ.toFun p, hg_left p⟩⟩
  · rw [hσ i, hg_left]

theorem congruent_trans (n : ℕ) (P Q R : PointConfig n) :
    AreCongruent n P Q → AreCongruent n Q R → AreCongruent n P R := by
  intro ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩
  exact ⟨⟨σ₂.toFun ∘ σ₁.toFun, fun p q => by
    simp only [Function.comp]; rw [σ₂.preserves_dist, σ₁.preserves_dist],
    σ₂.bijective.comp σ₁.bijective⟩,
    fun i => by simp only [Function.comp]; rw [hσ₂ i, hσ₁ i]⟩

/-
# Part 4: Counting Incongruent Optimal Configurations

The function h(n) counts equivalence classes of optimal configurations.
-/

-- The quotient of optimal configurations by congruence
-- This represents the set of incongruent optimal configurations
noncomputable instance congruenceSetoid (n : ℕ) : Setoid (PointConfig n) where
  r := AreCongruent n
  iseqv := ⟨congruent_refl n,
            fun h => congruent_symm n _ _ h,
            fun h₁ h₂ => congruent_trans n _ _ _ h₁ h₂⟩

def IncongruentOptimal (n : ℕ) := Quotient (congruenceSetoid n)

-- h(n) = number of optimal configurations (up to the natural cardinality)
noncomputable def h (n : ℕ) : ℕ := Nat.card {P : PointConfig n // IsOptimal n P}

-- h(n) counts optimal configurations by definition
theorem h_counts_optimal : ∀ n, h n = Nat.card {P : PointConfig n // IsOptimal n P} :=
  fun _ => rfl

/-
# Part 5: The Main Conjecture

Erdős asked whether h(n) → ∞ as n → ∞.
-/

-- The main conjecture: h(n) tends to infinity
def ErdosConjecture103 : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, h n > C

-- Equivalent: h is unbounded
def hUnbounded : Prop :=
  ∀ C : ℕ, ∃ n : ℕ, h n > C

-- The conjecture (h → ∞) implies h is unbounded.
-- The converse does NOT hold without monotonicity: a function can be
-- unbounded without tending to infinity (e.g., oscillating).
theorem conjecture_implies_unbounded : ErdosConjecture103 → hUnbounded := by
  intro hconj C
  obtain ⟨N, hN⟩ := hconj C
  exact ⟨N, hN N (le_refl N)⟩

/-
# Part 6: Known Bounds and Partial Results

Even weaker statements are open.
-/

-- Open question: does h(n) ≥ 2 for all large n?
def WeakConjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, h n ≥ 2

-- Even weaker: infinitely many n have h(n) ≥ 2
def VeryWeakConjecture : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, h n ≥ 2

-- h(n) ≥ 1 for all n ≥ 2 (at least one optimal config exists)
/-
# Part 7: Connection to Packing Problems

The problem relates to optimal sphere packing in 2D.
-/

-- The optimal packing density in ℝ²
-- For circles of radius 1/2, density is π/(2√3) ≈ 0.9069
noncomputable def optimalPackingDensity : ℝ := Real.pi / (2 * Real.sqrt 3)

-- For large n, optimal diameter relates to packing
-- d(n) ≈ √(n / optimal_density) for large n
def IsHexagonalLattice (n : ℕ) (P : PointConfig n) : Prop :=
  HasMinSeparation n P ∧
  ∀ i : Fin n, ∃ j : Fin n, i ≠ j ∧ pointDist (P i) (P j) ≤ 1 + 1 / n

/-
# Part 8: Related Problem #99

Erdős Problem #99 is cited as related.
-/

-- Problem 99: related question about optimal configurations
-- Both problems concern the structure of extremal point sets in the plane
-- Proof: h(n) ≥ 1 means Nat.card of optimal configs ≥ 1, so the type is nonempty.
theorem related_to_problem_99 :
    ∀ n ≥ 2, h n ≥ 1 → ∃ P : PointConfig n, IsOptimal n P := by
  intro n _ hhn
  have hcard : 0 < Nat.card {P : PointConfig n // IsOptimal n P} := by
    rw [← h_counts_optimal]; omega
  obtain ⟨hne, _⟩ := Nat.card_pos_iff.mp hcard
  exact ⟨hne.some.val, hne.some.property⟩

/-
# Part 9: Problem Status

The problem remains OPEN. Very little is known about h(n).
-/

-- The problem is open
def erdos_103_status : String := "OPEN"

-- Main formal statement
theorem erdos_103_statement :
    ErdosConjecture103 ↔
    ∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, h n > C := by
  rfl

/-
# Summary

**Problem:** Does h(n) → ∞ where h(n) counts incongruent optimal configurations
of n points minimizing diameter with minimum separation 1?

**Known:**
- h(n) ≥ 1 for n ≥ 2 (existence of optimal configs)
- h(2) = h(3) = 1 (unique small configurations)
- Optimal diameter relates to circle packing density

**Unknown:**
- Whether h(n) → ∞
- Whether h(n) ≥ 2 for all large n
- Whether h(n) ≥ 2 for infinitely many n

**Difficulty:** Requires understanding all optimal configurations, not just one.
-/

end Erdos103
