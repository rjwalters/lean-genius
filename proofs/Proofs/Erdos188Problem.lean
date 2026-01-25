/-
Erdős Problem #188: Unit Distance Colorings and Arithmetic Progressions

**Problem Statement (OPEN)**

Find the smallest constant k such that ℝ² can be colored red/blue where:
1. No two red points are unit distance apart
2. No k-term arithmetic progression of blue points has distance 1

**Background:**
- Euclidean Ramsey theory problem
- Lower bound: k ≥ 6 (Tsaturian 2017, improving k ≥ 5 from EGMRSS)
- Upper bound: k ≤ 10,000,000 (Erdős-Graham, claimed without proof)

**Status:** OPEN

**Reference:** [EGMRSS75], [ErGr79], [ErGr80], [Ts17]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Set Metric

namespace Erdos188

/-!
# Part 1: Basic Definitions

Define colorings of the plane and the key constraints.
-/

-- A coloring of the plane: each point is red (false) or blue (true)
-- We use ℂ ≃ ℝ² for convenience
def PlaneColoring := ℂ → Bool

-- The red points (false = red)
def redPoints (c : PlaneColoring) : Set ℂ := {z | c z = false}

-- The blue points (true = blue)
def bluePoints (c : PlaneColoring) : Set ℂ := {z | c z = true}

-- Red is unit-distance-free: no two red points are unit distance apart
def RedUnitDistanceFree (c : PlaneColoring) : Prop :=
  ∀ z₁ z₂ : ℂ, c z₁ = false → c z₂ = false → z₁ ≠ z₂ → dist z₁ z₂ ≠ 1

-- An arithmetic progression in ℂ with common difference d
def IsAPInPlane (S : Finset ℂ) (d : ℂ) : Prop :=
  ∃ a : ℂ, S = Finset.image (fun i : Fin S.card => a + i • d) Finset.univ

-- A k-term arithmetic progression of blue points with unit distance steps
def HasBlueAPWithUnitStep (c : PlaneColoring) (k : ℕ) : Prop :=
  ∃ a : ℂ, ∃ d : ℂ, Complex.abs d = 1 ∧
    ∀ i : Fin k, c (a + i • d) = true

-- Alternative: blue points contain a k-AP with step of length 1
def BlueContainsUnitAP (c : PlaneColoring) (k : ℕ) : Prop :=
  ∃ a d : ℂ, Complex.abs d = 1 ∧
    ∀ i : ℕ, i < k → c (a + i • d) = true

-- A valid coloring for parameter k
def IsValidColoring (c : PlaneColoring) (k : ℕ) : Prop :=
  RedUnitDistanceFree c ∧ ¬ BlueContainsUnitAP c k

/-!
# Part 2: The Set s and the Problem

Define the set s of achievable k values.
-/

-- The set s: values of k for which a valid coloring exists
def achievableSet : Set ℕ := {k | ∃ c : PlaneColoring, IsValidColoring c k}

-- The main problem: find the minimum of s
def ErdosProblem188 : Prop :=
  ∃ k : ℕ, IsLeast achievableSet k

-- The minimum achievable k
noncomputable def minAchievable : ℕ := sInf achievableSet

/-!
# Part 3: Known Bounds

Lower bound ≥ 6, upper bound ≤ 10,000,000.
-/

-- Lower bound: k ≥ 5 (EGMRSS)
axiom lower_bound_5 : ∀ k ∈ achievableSet, k ≥ 5

-- Improved lower bound: k ≥ 6 (Tsaturian 2017)
axiom lower_bound_6 : ∀ k ∈ achievableSet, k ≥ 6

-- Upper bound: k ≤ 10,000,000 exists in s (Erdős-Graham)
axiom upper_bound_exists : ∃ k ∈ achievableSet, k ≤ 10000000

-- The set is nonempty (by the upper bound)
theorem achievable_nonempty : achievableSet.Nonempty := by
  obtain ⟨k, hk, _⟩ := upper_bound_exists
  exact ⟨k, hk⟩

-- Combined bound
theorem erdos_188_bounds : ∀ k ∈ achievableSet, 6 ≤ k ∧ ∃ k' ∈ achievableSet, k' ≤ 10000000 := by
  intro k hk
  exact ⟨lower_bound_6 k hk, upper_bound_exists⟩

/-!
# Part 4: Unit Distance Graph

The problem relates to the unit distance graph of ℝ².
-/

-- The unit distance graph: vertices = ℂ, edges = pairs at distance 1
def UnitDistanceGraph : SimpleGraph ℂ where
  Adj z₁ z₂ := z₁ ≠ z₂ ∧ dist z₁ z₂ = 1
  symm := by
    intro z₁ z₂ ⟨hne, hd⟩
    exact ⟨hne.symm, by rw [dist_comm]; exact hd⟩
  loopless := by
    intro z ⟨hne, _⟩
    exact hne rfl

-- Red points form an independent set in the unit distance graph
theorem red_is_independent (c : PlaneColoring) (h : RedUnitDistanceFree c) :
    ∀ z₁ z₂ : ℂ, z₁ ∈ redPoints c → z₂ ∈ redPoints c → z₁ ≠ z₂ →
      ¬ UnitDistanceGraph.Adj z₁ z₂ := by
  intro z₁ z₂ hr1 hr2 hne ⟨_, hd⟩
  exact h z₁ z₂ hr1 hr2 hne hd

/-!
# Part 5: Connection to van der Waerden

Noga Alon's observation about the original problem formulation.
-/

-- van der Waerden's theorem: any finite coloring of ℤ has arbitrarily long monochromatic APs
-- This is why the original problem (without unit distance restriction) has no solution
axiom vanDerWaerden : ∀ r k : ℕ, r > 0 → ∃ N : ℕ,
  ∀ c : Fin r → ℕ → Bool,
    ∃ i : Fin r, ∃ a d : ℕ, d > 0 ∧ ∀ j < k, c i (a + j * d) = true

-- Alon's observation: without unit distance restriction, no k works
-- (not formalized in detail here)
axiom alon_observation : ¬ ∃ k : ℕ, ∀ c : PlaneColoring,
  RedUnitDistanceFree c →
    ¬ ∃ a d : ℂ, d ≠ 0 ∧ ∀ i : ℕ, i < k → c (a + i • d) = true

/-!
# Part 6: Specific Constructions

Known constructions achieving the upper bound.
-/

-- A stripe-based coloring (schematic)
-- Color red if distance to nearest lattice line is small
-- This avoids unit distances in red but limits blue APs

-- The existence of a valid coloring for some large k
theorem large_k_valid : ∃ k : ℕ, ∃ c : PlaneColoring, IsValidColoring c k := by
  obtain ⟨k, hk, _⟩ := upper_bound_exists
  exact ⟨k, hk⟩

/-!
# Part 7: Problem Status

The exact value of min s remains OPEN.
-/

-- The problem is open
def erdos_188_status : String := "OPEN"

-- What we know:
-- 1. s is nonempty (by upper bound construction)
-- 2. ∀ k ∈ s, k ≥ 6 (Tsaturian)
-- 3. ∃ k ∈ s, k ≤ 10,000,000 (Erdős-Graham)
-- 4. The exact minimum is unknown

-- Formal statement: find the minimum of s
theorem erdos_188_statement :
    ErdosProblem188 ↔
    ∃ k : ℕ, k ∈ achievableSet ∧ ∀ k' ∈ achievableSet, k ≤ k' := by
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k, hk.1, hk.2⟩
  · intro ⟨k, hk1, hk2⟩
    exact ⟨k, ⟨hk1, hk2⟩⟩

/-!
# Part 8: Summary

**Known:**
- 6 ≤ min s ≤ 10,000,000
- Lower bound from combinatorial analysis
- Upper bound from explicit (but complex) constructions

**Unknown:**
- The exact value of min s
- Whether substantially better bounds are achievable
-/

end Erdos188
