/-
  Erdős Problem #35: Schnirelmann Density and Additive Bases

  Source: https://erdosproblems.com/35
  Status: SOLVED (Plünnecke, 1970)

  Statement:
  Let B ⊆ ℕ be an additive basis of order k with 0 ∈ B. Is it true that
  for every A ⊆ ℕ we have
    d_s(A + B) ≥ α + α(1-α)/k
  where α = d_s(A) and d_s(A) = inf_{N≥1} |A ∩ {1,...,N}| / N is the
  Schnirelmann density?

  Solution:
  - Erdős (1936): Proved with 2k instead of k in denominator
  - Plünnecke (1970): Proved the stronger d_s(A + B) ≥ α^{1-1/k}
  - Ruzsa observed this immediately implies the original conjecture

  References:
  - [Er36c] Erdős's 1936 paper
  - [Er56] Problem formulation
  - [Pl70] Plünnecke's theorem

  Tags: number-theory, additive-combinatorics, density
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Erdos35

open Set

/- ## Part I: Schnirelmann Density -/

/-- The counting function: number of elements of A in {1, ..., N}. -/
def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.filter (· ∈ A) (Finset.range (N + 1) \ {0})).card

/-- The ratio |A ∩ {1,...,N}| / N for N ≥ 1. -/
noncomputable def densityRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  if N = 0 then 1 else (countingFunction A N : ℝ) / N

/-- Schnirelmann density: the infimum of |A ∩ {1,...,N}| / N over all N ≥ 1. -/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  ⨅ N : {n : ℕ // n ≥ 1}, densityRatio A N

/-- Notation: d_s(A) for Schnirelmann density. -/
notation "d_s" => schnirelmannDensity

/- ## Part II: Additive Bases -/

/-- The sumset A + B = {a + b : a ∈ A, b ∈ B}. -/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

instance : HAdd (Set ℕ) (Set ℕ) (Set ℕ) where
  hAdd := sumset

/-- The k-fold sumset: B + B + ... + B (k times). -/
def kFoldSum (B : Set ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | 1 => B
  | n + 1 => sumset (kFoldSum B n) B

/-- B is an additive basis of order k if every natural number is a sum
    of at most k elements of B. -/
def IsAdditiveBasis (B : Set ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ∃ m ≤ k, n ∈ kFoldSum B m

/-- B is an additive basis of order exactly k if k is minimal. -/
def IsAdditiveBasisExact (B : Set ℕ) (k : ℕ) : Prop :=
  IsAdditiveBasis B k ∧ ¬IsAdditiveBasis B (k - 1)

/- ## Part III: Basic Properties -/

/-- Schnirelmann density is always in [0, 1]. -/
theorem schnirelmannDensity_nonneg (A : Set ℕ) : 0 ≤ d_s A := by
  unfold schnirelmannDensity densityRatio
  apply Real.iInf_nonneg
  intro ⟨N, hN⟩
  split_ifs with h
  · exact zero_le_one
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _

theorem schnirelmannDensity_le_one (A : Set ℕ) : d_s A ≤ 1 := by
  unfold schnirelmannDensity
  apply ciInf_le_of_le ⟨⟨1, le_refl 1⟩⟩
  unfold densityRatio
  simp only [↓reduceIte, Nat.cast_one, div_one]
  -- countingFunction A 1 ≤ 1 since we only count in {1}
  sorry

/-- If 1 ∈ A, then d_s(A) > 0 is possible but not guaranteed. -/
theorem density_pos_of_one_mem (A : Set ℕ) (h : 1 ∈ A) :
    densityRatio A 1 = 1 := by
  unfold densityRatio countingFunction
  simp only [↓reduceIte, Nat.cast_one, div_one]
  -- {1} \ {0} filtered by (· ∈ A) has card 1 when 1 ∈ A
  sorry

/-- Adding a basis can only increase density. -/
theorem density_mono_sumset (A B : Set ℕ) (h0 : 0 ∈ B) :
    d_s A ≤ d_s (A + B) := by
  -- A ⊆ A + B when 0 ∈ B, so density increases
  sorry

/- ## Part IV: Erdős's Original Result -/

/-- Erdős (1936): d_s(A + B) ≥ α + α(1-α)/(2k).

This is a weaker version with 2k in the denominator.
-/
theorem erdos_1936_bound (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis B k) (h0 : 0 ∈ B) :
    d_s (A + B) ≥ d_s A + d_s A * (1 - d_s A) / (2 * k) := by
  sorry

/- ## Part V: Plünnecke's Inequality -/

/-- Plünnecke's Inequality (1970): d_s(A + B) ≥ α^{1-1/k}.

This is the key result that implies Erdős's conjecture.
-/
theorem plunnecke_inequality (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis B k) (h0 : 0 ∈ B) :
    d_s (A + B) ≥ (d_s A) ^ (1 - 1 / (k : ℝ)) := by
  sorry

/-- Auxiliary lemma: α^{1-1/k} ≥ α + α(1-α)/k for α ∈ [0,1]. -/
theorem power_bound_implies_erdos (α : ℝ) (k : ℕ) (hk : k ≥ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α ^ (1 - 1 / (k : ℝ)) ≥ α + α * (1 - α) / k := by
  -- This is a calculus exercise
  -- For k = 1: LHS = α^0 = 1, RHS = α + α(1-α) = α(2-α) ≤ 1 ✓
  -- General case uses convexity/concavity arguments
  sorry

/- ## Part VI: The Main Theorem -/

/-- Erdős Problem #35: SOLVED.

If B is an additive basis of order k with 0 ∈ B, then for any A ⊆ ℕ,
  d_s(A + B) ≥ α + α(1-α)/k
where α = d_s(A).

This follows immediately from Plünnecke's inequality.
-/
theorem erdos_35 (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis B k) (h0 : 0 ∈ B) :
    d_s (A + B) ≥ d_s A + d_s A * (1 - d_s A) / k := by
  have hPlunnecke := plunnecke_inequality A B k hk hB h0
  have hBound := power_bound_implies_erdos (d_s A) k hk
    (schnirelmannDensity_nonneg A) (schnirelmannDensity_le_one A)
  linarith

/- ## Part VII: Special Cases -/

/-- When k = 1, B = ℕ and A + B = ℕ (after sufficient point). -/
theorem basis_order_one (B : Set ℕ) (hB : IsAdditiveBasis B 1) (h0 : 0 ∈ B) :
    B = Set.univ := by
  -- If every n is a sum of at most 1 element of B, then B = ℕ
  ext n
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨m, hm, hn⟩ := hB n
    interval_cases m
    · simp only [kFoldSum] at hn; simp only [mem_singleton_iff] at hn; omega
    · simp only [kFoldSum] at hn; exact hn

/-- The squares form an additive basis of order 4 (Lagrange). -/
def squares : Set ℕ := {n | ∃ m : ℕ, n = m^2}

theorem squares_basis_order_4 : IsAdditiveBasis squares 4 := by
  -- Lagrange's four-square theorem
  sorry

/-- The primes (with 1) form an additive basis of order 3 (Vinogradov + Goldbach). -/
def primesWithOne : Set ℕ := {1} ∪ {p | Nat.Prime p}

-- This requires Goldbach (unproven) for even numbers, but Vinogradov gives order 4
theorem primes_basis_conditional : IsAdditiveBasis primesWithOne 3 := by
  -- Conditional on Goldbach
  sorry

end Erdos35

/-
  ## Summary

  This file formalizes Erdős Problem #35 on Schnirelmann density and
  additive bases.

  **Status**: SOLVED

  **The Conjecture**: If B is an additive basis of order k with 0 ∈ B,
  then d_s(A + B) ≥ α + α(1-α)/k where α = d_s(A).

  **Solution History**:
  - Erdős (1936): Proved with 2k in denominator
  - Plünnecke (1970): Proved d_s(A + B) ≥ α^{1-1/k}
  - Ruzsa: Observed Plünnecke implies the original conjecture

  **What we formalize**:
  1. Schnirelmann density definition and basic properties
  2. Additive basis of order k
  3. Erdős's 1936 partial result
  4. Plünnecke's inequality
  5. The derivation of Erdős's conjecture from Plünnecke
  6. Special cases: squares (order 4), primes (conditional)

  **Key sorries**:
  - `plunnecke_inequality`: The main 1970 result
  - `power_bound_implies_erdos`: Calculus lemma α^{1-1/k} ≥ α + α(1-α)/k
  - `squares_basis_order_4`: Lagrange's four-square theorem

  **Note**: The main theorem `erdos_35` compiles modulo the sorries,
  showing the logical structure of how Plünnecke implies Erdős.
-/
