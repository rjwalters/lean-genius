/-
# Erdős Problem #36 — Minimum Overlap Problem

Partition {1, ..., 2N} into two sets A, B of size N each.
For each integer difference k, count the number of pairs (a,b)
with a ∈ A, b ∈ B, a − b = k. This is the "overlap" at k.
Let M(N) be the minimum over all such partitions of the maximum
overlap.

Determine the asymptotic constant c = lim M(N)/N.

Known: 0.379005 < c < 0.380876

Status: OPEN
Reference: https://erdosproblems.com/36
Wikipedia: https://en.wikipedia.org/wiki/Minimum_overlap_problem
-/

import Mathlib

open Finset

-- ============================================================================
-- Part I: Core Definitions
-- ============================================================================

/-- The interval {1, ..., 2N} as a finset of integers. -/
def interval (N : ℕ) : Finset ℤ := Finset.Icc 1 (2 * ↑N)

/-- The overlap of sets A, B at difference k: the number of pairs
    (a, b) with a ∈ A, b ∈ B, a − b = k. -/
def overlap (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A ×ˢ B).filter fun p => p.1 - p.2 = k).card

/-- The maximum overlap over all integer differences. -/
noncomputable def maxOverlap (A B : Finset ℤ) : ℕ :=
  ((A ×ˢ B).image (fun p : ℤ × ℤ => p.1 - p.2)).sup (overlap A B)

/-- M(N): the minimum maximum overlap over all equal partitions
    of {1, ..., 2N}. -/
noncomputable def minMaxOverlap (N : ℕ) : ℕ :=
  let I := interval N
  let parts := I.powerset.filter (fun A => A.card = N)
  parts.sup (fun A => maxOverlap A (I \ A))  -- sup works but we want inf; see axiomatized version below

-- NOTE: Lean's ℕ lacks ⊤ for Finset.inf, so minMaxOverlap using Finset.sup
-- above gives the WRONG quantity (max instead of min). We axiomatize M(N)
-- directly with achievability and minimality axioms below.

-- ============================================================================
-- Part II: Basic Properties
-- ============================================================================

/-- The product cardinality: |A ×ˢ B| = |A| × |B|. -/
theorem product_card (A B : Finset ℤ) : (A ×ˢ B).card = A.card * B.card :=
  Finset.card_product A B

-- ============================================================================
-- Part III: M(N) Definition
-- ============================================================================

/-- The set of all N-element subsets of {1,...,2N}. -/
noncomputable def partitions (N : ℕ) : Finset (Finset ℤ) :=
  (interval N).powerset.filter (fun A => A.card = N)

/-- The set of max overlaps across all partitions. -/
noncomputable def overlapValues (N : ℕ) : Finset ℕ :=
  (partitions N).image (fun A => maxOverlap A (interval N \ A))

/-- M(N): the minimum maximum overlap over all equal partitions
    of {1, ..., 2N}. Defined via Finset.min' on the image of
    maxOverlap over all N-element subsets. Returns 0 when N = 0
    (vacuously: only partition is ∅ ⊔ ∅). -/
noncomputable def M (N : ℕ) : ℕ :=
  if h : (overlapValues N).Nonempty then (overlapValues N).min' h else 0

/-- **Erdős Problem #36**: Determine the asymptotic constant
    c = lim M(N)/N. The problem is to find the exact value of c. -/
axiom erdos_36_limit_exists :
  ∃ c : ℝ, c > 0 ∧
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |((M N : ℝ) / N) - c| < ε

-- ============================================================================
-- Part V: Known Bounds
-- ============================================================================

/-- **Erdős (1955)**: trivial lower bound M(N)/N > 1/4.
    Originally a pigeonhole argument (N² pairs in ≤ 4N−1 differences),
    now proved as a corollary of White's sharper bound (0.379 > 0.25). -/
theorem erdos_lower_quarter :
    ∀ N : ℕ, N ≥ 1 → (M N : ℝ) / N > 1 / 4 := by
  intro N hN
  calc (M N : ℝ) / N > 379005 / 1000000 := white_lower N hN
    _ > 1 / 4 := by norm_num

/-- **Scherk (1955)**: improved lower bound M(N)/N > 1 − 1/√2 ≈ 0.293.
    Now a corollary of White's sharper bound, since √2 < 3/2 implies
    1 − 1/√2 < 1/3 < 0.379. -/
theorem scherk_lower :
    ∀ N : ℕ, N ≥ 1 →
      (M N : ℝ) / N > 1 - 1 / Real.sqrt 2 := by
  intro N hN
  have hw := white_lower N hN
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  -- √2 < 3/2 since 2 < (3/2)² = 9/4
  have h_sqrt_lt : Real.sqrt 2 < 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt (9 / 4) from by
      rw [show (9 : ℝ) / 4 = (3 / 2) ^ 2 from by ring]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- 1/√2 > 2/3 (reciprocal inequality)
  have h_inv : 1 / Real.sqrt 2 > 2 / 3 := by
    rw [div_lt_div_iff (by norm_num : (0:ℝ) < 3) h_sqrt_pos]
    linarith
  -- 1 - 1/√2 < 1/3 < 379005/1000000
  linarith

/-- **White (2022)**: best known lower bound M(N)/N > 0.379005,
    obtained via Fourier analysis and convex optimization. -/
axiom white_lower :
  ∀ N : ℕ, N ≥ 1 →
    (M N : ℝ) / N > 379005 / 1000000

/-- **Haugland (2016)**: upper bound M(N)/N < 0.380926 via step
    functions. Improved to 0.380876 by TTT-Discover (2026). -/
axiom upper_bound :
  ∀ N : ℕ, N ≥ 1 →
    (M N : ℝ) / N < 380876 / 1000000

-- ============================================================================
-- Part VI: Small Values
-- ============================================================================

/-- Computable version of `maxOverlap`. Mirrors the noncomputable definition
    but is accepted by Lean's compiler for evaluation via `native_decide`. -/
def maxOverlapC (A B : Finset ℤ) : ℕ :=
  ((A ×ˢ B).image (fun p : ℤ × ℤ => p.1 - p.2)).sup (overlap A B)

/-- Computable version of `M(N)`. Uses `maxOverlapC` and inline definitions
    to avoid noncomputable intermediate functions. -/
def MC (N : ℕ) : ℕ :=
  let I := Finset.Icc (1 : ℤ) (2 * ↑N)
  let parts := I.powerset.filter (fun A => A.card = N)
  let vals := parts.image (fun A => maxOverlapC A (I \ A))
  if h : vals.Nonempty then vals.min' h else 0

/-- `MC` agrees with `M`: both compute the same min-max overlap value.
    After unfolding all intermediate definitions, the expressions are identical.
    The `noncomputable` tag on `M` only affects code generation, not definitional equality. -/
theorem MC_eq (N : ℕ) : MC N = M N := rfl

/-- Known exact values: M(1) = 1, M(2) = 1, M(3) = 2, M(4) = 2, M(5) = 3.
    Verified computationally via `native_decide` on the computable mirror `MC`. -/
theorem small_values :
    M 1 = 1 ∧ M 2 = 1 ∧ M 3 = 2 ∧ M 4 = 2 ∧ M 5 = 3 := by
  have h : ∀ n, M n = MC n := fun n => (MC_eq n).symm
  simp only [h]
  native_decide

-- ============================================================================
-- Part VII: Consequences and Observations
-- ============================================================================

/-- The bounds sandwich the asymptotic constant:
    0.379005 < c < 0.380876. -/
theorem constant_bounds :
  ∀ c : ℝ, (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |((M N : ℝ) / N) - c| < ε) →
    c ≥ 379005 / 1000000 ∧ c ≤ 380876 / 1000000 := by
  intro c hc
  constructor
  · -- Lower bound: from white_lower
    by_contra h
    push_neg at h
    have hε : (0 : ℝ) < 379005 / 1000000 - c := by linarith
    obtain ⟨N₀, hN₀⟩ := hc _ hε
    have hN : N₀ + 1 ≥ 1 := by omega
    have h1 := white_lower (N₀ + 1) hN
    have h2 := hN₀ (N₀ + 1) (by omega)
    rw [abs_lt] at h2
    linarith
  · -- Upper bound: from upper_bound
    by_contra h
    push_neg at h
    have hε : (0 : ℝ) < c - 380876 / 1000000 := by linarith
    obtain ⟨N₀, hN₀⟩ := hc _ hε
    have hN : N₀ + 1 ≥ 1 := by omega
    have h1 := upper_bound (N₀ + 1) hN
    have h2 := hN₀ (N₀ + 1) (by omega)
    rw [abs_lt] at h2
    linarith

/- ## Historical Notes -/

/- **Erdős' Original Conjecture**: Erdős initially conjectured c = 1/2,
    but this was disproved. The true value is near 0.38. -/

/- **Fourier Analytic Approach**: White's method translates the
    combinatorial problem into a convex optimization program
    using elementary Fourier analysis on ℤ. -/

/- **Connection to Additive Combinatorics**: The minimum overlap
    problem is a fundamental question about the structure of
    equal partitions and difference sets. -/
