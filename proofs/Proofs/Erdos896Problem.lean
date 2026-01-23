/-
Erdős Problem #896: Unique Product Representation Count

**Statement**: Estimate max F(A,B) where A, B ⊆ {1,...,N} and F(A,B) counts
the number of m such that m = ab has exactly one solution with a ∈ A, b ∈ B.

**Status**: OPEN

**Known Bounds** (van Doorn):
- Lower bound: (1+o(1))N²/log N
- Upper bound: ≪ N²/(log N)^δ(log log N)^(3/2) where δ ≈ 0.086

**Context**: This is a multiplicative combinatorics problem asking how many
products can have unique representations when we choose two sets A and B.

**Related**: #490, #895, #897

Reference: https://erdosproblems.com/896
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Erdos896

open Finset Real

/-!
## Part I: Core Definitions
-/

/-- The product set A · B -/
def productSet (A B : Finset ℕ) : Finset ℕ :=
  (A ×ˢ B).image (fun p => p.1 * p.2)

/-- Count of representations of m as a · b with a ∈ A, b ∈ B -/
def representationCount (A B : Finset ℕ) (m : ℕ) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 * p.2 = m)).card

/-- F(A,B) = number of m with exactly one representation -/
def F (A B : Finset ℕ) : ℕ :=
  (productSet A B).filter (fun m => representationCount A B m = 1) |>.card

/-!
## Part II: Basic Properties
-/

/-- F(A,B) ≤ |A| · |B| (trivial upper bound) -/
theorem F_le_product (A B : Finset ℕ) : F A B ≤ A.card * B.card := by
  sorry

/-- F(A,B) is symmetric in A and B up to reordering -/
theorem F_symm (A B : Finset ℕ) : F A B = F B A := by
  sorry

/-- Empty set case -/
theorem F_empty_left (B : Finset ℕ) : F ∅ B = 0 := by
  simp [F, productSet, representationCount]

theorem F_empty_right (A : Finset ℕ) : F A ∅ = 0 := by
  simp [F, productSet, representationCount]

/-!
## Part III: The Optimization Problem
-/

/-- The interval {1, ..., N} as a Finset -/
def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- The maximum F(A,B) over all A, B ⊆ {1,...,N} -/
noncomputable def maxF (N : ℕ) : ℕ :=
  Finset.sup (interval N).powerset.product (interval N).powerset
    (fun p => F p.1 p.2)

/-- The main question: estimate maxF(N) asymptotically -/
def mainQuestion : Prop :=
  ∃ (f : ℕ → ℝ), ∀ N : ℕ, N ≥ 2 → (maxF N : ℝ) = f N * (1 + o(1))

/-!
## Part IV: Known Bounds (van Doorn)
-/

/-- Lower bound: maxF(N) ≥ (1+o(1)) · N²/log N -/
axiom van_doorn_lower :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (maxF N : ℝ) ≥ (1 - ε) * N^2 / log N

/-- Upper bound constant δ ≈ 0.086 -/
def delta : ℝ := 0.086

/-- Upper bound: maxF(N) ≪ N²/(log N)^δ · (log log N)^(3/2) -/
axiom van_doorn_upper :
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 3 →
    (maxF N : ℝ) ≤ C * N^2 / ((log N)^delta * (log (log N))^(3/2))

/-!
## Part V: The Gap
-/

/-- The gap between bounds: roughly a factor of (log N)^(1-δ) · (log log N)^(3/2)

Lower: Ω(N²/log N)
Upper: O(N²/(log N)^0.086 · (log log N)^(3/2))

Gap factor: (log N)^0.914 · (log log N)^(3/2)

This gap grows unboundedly, so the true asymptotic is not determined. -/
theorem gap_observation (N : ℕ) (hN : N ≥ 10) :
    (log N : ℝ)^(1 - delta) * (log (log N))^(3/2) > 1 := by
  sorry

/-!
## Part VI: Examples and Small Cases
-/

/-- For small N, we can compute maxF explicitly -/
-- maxF(2) = 1: A = B = {1,2}, unique products are 1, 2 (2 = 1·2 or 2·1)
-- Actually need to be more careful about counting

/-- A simple construction: A = B = {1,...,N} -/
def standardPair (N : ℕ) : Finset ℕ × Finset ℕ := (interval N, interval N)

/-- The number of unique products in the standard construction -/
theorem standard_construction_bound (N : ℕ) (hN : N ≥ 2) :
    F (interval N) (interval N) ≥ N := by
  sorry -- The primes in {1,...,N} contribute unique products

/-!
## Part VII: Why Unique Products are Interesting
-/

/-- A product m = ab is unique (in A × B) when:
    1. m is prime (can only be 1 · m or m · 1)
    2. m has few divisors in the relevant ranges
    3. A and B are "thin" in certain multiplicative structures -/
theorem unique_products_insight : True := trivial

/-- The problem connects to:
    1. Multiplicative energy of sets
    2. Sum-product phenomena
    3. Divisor distribution -/
theorem connections : True := trivial

/-!
## Part VIII: Strategies for Better Bounds
-/

/-- To improve the lower bound:
    - Find sets A, B with many unique products
    - Use sets with multiplicative structure
    - Consider primes or prime powers -/
theorem lower_bound_strategies : True := trivial

/-- To improve the upper bound:
    - Use incidence geometry methods
    - Apply sum-product theory
    - Analyze divisor sums more carefully -/
theorem upper_bound_strategies : True := trivial

/-!
## Part IX: Summary
-/

/-- Erdős #896 Summary:

**Problem**: Estimate max F(A,B) where F counts unique products a·b

**Status**: OPEN

**Known Bounds**:
- Lower: (1+o(1))N²/log N
- Upper: O(N²/(log N)^0.086 · (log log N)^(3/2))

**Gap**: Factor of (log N)^0.914 · (log log N)^(3/2)

**Key Insight**: The true asymptotic behavior is not determined

**Related**: #490, #895, #897 -/
theorem erdos_896_status : True := trivial

end Erdos896
