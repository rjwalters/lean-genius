/-
Erdős Problem #421: Distinct Products in Dense Sequences

**Problem Statement (OPEN)**

Is there a sequence 1 ≤ d₁ < d₂ < ... with density 1 such that all products
∏_{u ≤ i ≤ v} dᵢ are distinct?

**Known Results:**
- Selfridge: exists sequence with density > 1/e - ε for any ε > 0

**Status:** OPEN

**Reference:** [ErGr80, p.84]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Set Finset BigOperators Nat Filter

namespace Erdos421

/-!
# Part 1: Basic Definitions

Define strictly increasing sequences and density.
-/

-- A sequence d : ℕ → ℕ starting from 1
-- We want d strictly increasing: d(0) < d(1) < d(2) < ...

-- Strictly increasing sequence
def IsStrictlyIncreasing (d : ℕ → ℕ) : Prop := StrictMono d

-- Sequence starts at least 1
def StartsAtOne (d : ℕ → ℕ) : Prop := 1 ≤ d 0

-- Valid sequence: strictly increasing starting at 1
def IsValidSequence (d : ℕ → ℕ) : Prop :=
  IsStrictlyIncreasing d ∧ StartsAtOne d

/-!
# Part 2: Density of Sequences

Density 1 means the sequence contains "almost all" integers asymptotically.
-/

-- Counting function: number of terms ≤ n
noncomputable def countingFunc (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun k => k ∈ Set.range d) |>.card

-- Alternative: for strictly increasing d, count is max {i : d(i) ≤ n}
noncomputable def indexUpTo (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.find (⟨n + 1, fun h => by omega⟩ : ∃ i, n < d i)

-- Density definition: limit of countingFunc(n)/n as n → ∞
def HasDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun n => (S ∩ Finset.range (n + 1)).toFinite.toFinset.card / (n + 1 : ℝ))
    atTop (nhds δ)

-- Density 1 means the sequence has natural density 1
def HasDensityOne (d : ℕ → ℕ) : Prop := HasDensity (Set.range d) 1

/-!
# Part 3: Interval Products

Products of the form ∏_{u ≤ i ≤ v} d_i.
-/

-- Product over an interval [u, v]
def intervalProduct (d : ℕ → ℕ) (u v : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc u v, d i

-- All interval products
def AllIntervalProducts (d : ℕ → ℕ) : Set ℕ :=
  {p | ∃ u v : ℕ, u ≤ v ∧ p = intervalProduct d u v}

-- The set of valid pairs (u, v)
def ValidPairs : Set (ℕ × ℕ) := {p | p.1 ≤ p.2}

-- Map from pairs to products
def productMap (d : ℕ → ℕ) : ℕ × ℕ → ℕ :=
  fun p => intervalProduct d p.1 p.2

/-!
# Part 4: Distinctness of Products

All interval products must be distinct.
-/

-- Products are distinct: different pairs give different products
def HasDistinctProducts (d : ℕ → ℕ) : Prop :=
  ValidPairs.InjOn (productMap d)

-- Equivalent: for all (u₁,v₁) ≠ (u₂,v₂), products differ
def HasDistinctProductsAlt (d : ℕ → ℕ) : Prop :=
  ∀ u₁ v₁ u₂ v₂, u₁ ≤ v₁ → u₂ ≤ v₂ → (u₁, v₁) ≠ (u₂, v₂) →
    intervalProduct d u₁ v₁ ≠ intervalProduct d u₂ v₂

-- Equivalence of definitions
theorem distinct_equiv (d : ℕ → ℕ) :
    HasDistinctProducts d ↔ HasDistinctProductsAlt d := by
  constructor
  · intro h u₁ v₁ u₂ v₂ huv₁ huv₂ hne heq
    have : (u₁, v₁) = (u₂, v₂) := h huv₁ huv₂ heq
    exact hne this
  · intro h p₁ hp₁ p₂ hp₂ heq
    by_contra hne
    exact h p₁.1 p₁.2 p₂.1 p₂.2 hp₁ hp₂ hne heq

/-!
# Part 5: The Main Conjecture

Existence of a density-1 sequence with distinct products.
-/

-- The main conjecture
def ErdosConjecture421 : Prop :=
  ∃ d : ℕ → ℕ, IsValidSequence d ∧ HasDensityOne d ∧ HasDistinctProducts d

-- Alternative statement using the formal-conjectures style
theorem erdos_421_statement :
    ErdosConjecture421 ↔
    ∃ d : ℕ → ℕ, StrictMono d ∧ 1 ≤ d 0 ∧ HasDensity (Set.range d) 1 ∧
      ValidPairs.InjOn (productMap d) := by
  rfl

/-!
# Part 6: Selfridge's Construction

Selfridge showed a sequence exists with density > 1/e - ε.
-/

-- Selfridge's bound: achievable density
noncomputable def selfridgeDensity : ℝ := 1 / Real.exp 1  -- 1/e ≈ 0.3679

-- Selfridge's result: for any ε > 0, exists sequence with distinct products
-- and density > 1/e - ε
axiom selfridge_construction : ∀ ε > 0, ∃ d : ℕ → ℕ,
  IsValidSequence d ∧ HasDistinctProducts d ∧
  ∃ δ : ℝ, δ > selfridgeDensity - ε ∧ HasDensity (Set.range d) δ

-- Selfridge achieves density 1/e asymptotically
theorem selfridge_achieves_one_over_e :
    ∀ ε > 0, ∃ d : ℕ → ℕ, IsValidSequence d ∧ HasDistinctProducts d ∧
    ∃ δ : ℝ, δ > 1 / Real.exp 1 - ε ∧ HasDensity (Set.range d) δ :=
  selfridge_construction

/-!
# Part 7: Upper Bounds and Obstructions

Why can't we easily achieve density 1?
-/

-- If d has distinct products, there are constraints on gaps
-- Heuristically: many products means many distinct values, limiting growth

-- Number of interval products up to length n is ~n²/2
def numProductsUpToLength (n : ℕ) : ℕ := n * (n + 1) / 2

-- For products to be distinct, they must fit in the range of possible values
-- This constrains how dense the sequence can be

/-!
# Part 8: Simple Examples

Illustrate the definitions with examples.
-/

-- Natural numbers have density 1 but products are NOT distinct
-- e.g., 1*2*3 = 6 and 2*3 = 6 (but wait, those are different intervals...)
-- Actually: d_i = i+1, product [0,2] = 1*2*3 = 6, product [1,2] = 2*3 = 6
-- But [0,2] ≠ [1,2] as pairs, so they need different products

-- For natural numbers d(i) = i + 1:
-- intervalProduct [0,0] = 1
-- intervalProduct [1,1] = 2
-- intervalProduct [0,1] = 1*2 = 2  -- same as [1,1]!
-- So natural numbers fail distinctness

-- Primes might work better (each product is unique by prime factorization)
-- But primes have density 0, not 1

/-!
# Part 9: Related Problem 786

Problem 786 discusses Selfridge's construction in detail.
-/

-- Reference to related problem
def RelatedProblem786 : Prop := True  -- Selfridge's construction details

/-!
# Part 10: Problem Status

The problem remains OPEN.
-/

-- The problem is open
def erdos_421_status : String := "OPEN"

-- Summary of what's known
-- Best construction: Selfridge with density > 1/e - ε
-- Open: Can we achieve density 1?

-- OEIS sequences
-- A389544, A390848 are related

/-!
# Summary

**Problem:** Find a strictly increasing sequence d₁ < d₂ < ... starting from 1
with density 1 such that all products ∏_{u ≤ i ≤ v} d_i are distinct.

**Known:**
- Selfridge achieves density > 1/e - ε for any ε > 0
- Gap between 1/e and 1 remains

**Unknown:**
- Can density 1 be achieved?
- What is the supremum of achievable densities?

**Difficulty:** Balancing density (wanting many integers) against distinctness
(needing products to spread out).
-/

end Erdos421
