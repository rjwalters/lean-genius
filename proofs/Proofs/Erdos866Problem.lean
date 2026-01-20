/-
Erdős Problem #866: Pairwise Sums Threshold Function

Source: https://erdosproblems.com/866
Status: PARTIALLY SOLVED (specific cases solved, general open)

Statement:
For k ≥ 3, let g_k(N) be the minimal value such that if A ⊆ {1,...,2N}
has |A| ≥ N + g_k(N), then there exist integers b₁,...,b_k such that
all (k choose 2) pairwise sums b_i + b_j are in A (but the b_i themselves
need not be in A).

Known Results (Choi-Erdős-Szemerédi):
- g₃(N) = 2
- g₄(N) ≪ 1 (van Doorn: g₄(N) ≤ 2032)
- g₅(N) ≍ log N
- g₆(N) ≍ N^{1/2}
- General upper bound: g_k(N) ≪_k N^{1-2^{-k}}
- For large k and any ε > 0: g_k(N) > N^{1-ε}

The problem is to fully characterize g_k(N) for all k.

References:
- Choi, Erdős, Szemerédi, "On sums and products of integers" (unpublished)
- van Doorn, "On the pairwise sum problem" (2020s)

Tags: additive-combinatorics, sumsets, pairwise-sums, threshold-functions
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Finset Real

namespace Erdos866

/-! ## Part I: Basic Definitions -/

/-- The interval {1, 2, ..., 2N}. -/
def Interval (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => n ≥ 1)

/-- A set A has all pairwise sums of b₁,...,b_k if for all i < j,
    b_i + b_j ∈ A. -/
def HasAllPairwiseSums (A : Finset ℕ) (b : Fin k → ℤ) : Prop :=
  ∀ i j : Fin k, i < j → (b i + b j).toNat ∈ A

/-- The condition: A ⊆ {1,...,2N} and |A| ≥ N + g implies existence
    of b₁,...,b_k with all pairwise sums in A. -/
def PairwiseSumCondition (k N g : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Interval N → A.card ≥ N + g →
    ∃ b : Fin k → ℤ, HasAllPairwiseSums A b

/-- g_k(N) is the minimal g such that PairwiseSumCondition holds. -/
noncomputable def g (k N : ℕ) : ℕ :=
  Nat.find (⟨2 * N, by
    intro A hA hcard
    -- For sufficiently large g, the condition is vacuously true
    -- when no set can have that many elements
    sorry
  ⟩ : ∃ m, PairwiseSumCondition k N m)

/-! ## Part II: The Case k = 3 -/

/-- **Theorem (Choi-Erdős-Szemerédi):** g₃(N) = 2 for all N ≥ 1.

    If A ⊆ {1,...,2N} has |A| ≥ N + 2, then there exist integers
    b₁, b₂, b₃ such that b₁+b₂, b₁+b₃, b₂+b₃ ∈ A. -/
axiom g3_exact :
    ∀ N : ℕ, N ≥ 1 → g 3 N = 2

/-- The lower bound g₃(N) ≥ 2 comes from the set of odd numbers. -/
theorem g3_lower_bound (N : ℕ) (hN : N ≥ 1) : g 3 N ≥ 2 := by
  -- The set of odd numbers in {1,...,2N} has exactly N elements
  -- but no three integers have all pairwise sums odd
  -- (since two odds sum to even)
  sorry

/-! ## Part III: The Case k = 4 -/

/-- **Theorem (Choi-Erdős-Szemerédi):** g₄(N) is bounded by a constant.

    More precisely, g₄(N) ≤ C for some absolute constant C. -/
axiom g4_bounded :
    ∃ C : ℕ, ∀ N : ℕ, N ≥ 1 → g 4 N ≤ C

/-- **Theorem (van Doorn):** g₄(N) ≤ 2032.

    This is the current best known explicit bound. -/
axiom g4_vanDoorn :
    ∀ N : ℕ, N ≥ 1 → g 4 N ≤ 2032

/-! ## Part IV: The Case k = 5 -/

/-- **Theorem (Choi-Erdős-Szemerédi):** g₅(N) ≍ log N.

    There exist constants c₁, c₂ > 0 such that
    c₁ log N ≤ g₅(N) ≤ c₂ log N for large N. -/
axiom g5_asymptotic :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        c₁ * N.log ≤ g 5 N ∧ (g 5 N : ℝ) ≤ c₂ * N.log

/-- The lower bound g₅(N) ≥ c log N comes from the set of odd integers
    together with powers of 2. This set has about N + log₂ N elements
    but avoids the configuration. -/
theorem g5_lower_bound_construction :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (g 5 N : ℝ) ≥ c * N.log := by
  obtain ⟨c₁, c₂, hc1, hc2, N₀, hasym⟩ := g5_asymptotic
  exact ⟨c₁, hc1, N₀, fun N hN => (hasym N hN).1⟩

/-! ## Part V: The Case k = 6 -/

/-- **Theorem (Choi-Erdős-Szemerédi):** g₆(N) ≍ N^{1/2}.

    There exist constants c₁, c₂ > 0 such that
    c₁ √N ≤ g₆(N) ≤ c₂ √N for large N. -/
axiom g6_asymptotic :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        c₁ * (N : ℝ).sqrt ≤ g 6 N ∧ (g 6 N : ℝ) ≤ c₂ * (N : ℝ).sqrt

/-! ## Part VI: General Upper Bound -/

/-- **Theorem (Choi-Erdős-Szemerédi):** General upper bound.

    For all k ≥ 3, g_k(N) ≪_k N^{1-2^{-k}}.

    The implied constant depends on k. -/
axiom general_upper_bound :
    ∀ k : ℕ, k ≥ 3 →
      ∃ C : ℝ, C > 0 ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          (g k N : ℝ) ≤ C * (N : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k)

/-- The exponent 1 - 2^{-k} in the upper bound. -/
noncomputable def upperExponent (k : ℕ) : ℝ :=
  1 - (2 : ℝ)⁻¹ ^ k

theorem upperExponent_increasing (k : ℕ) (hk : k ≥ 1) :
    upperExponent k < upperExponent (k + 1) := by
  unfold upperExponent
  simp only [pow_succ]
  ring_nf
  sorry

/-! ## Part VII: General Lower Bound -/

/-- **Theorem (Choi-Erdős-Szemerédi):** For large k, g_k is nearly linear.

    For every ε > 0, if k is sufficiently large, then g_k(N) > N^{1-ε}. -/
axiom general_lower_bound :
    ∀ ε : ℝ, ε > 0 →
      ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          (g k N : ℝ) > (N : ℝ) ^ (1 - ε)

/-- The threshold grows toward N as k → ∞. -/
theorem threshold_approaches_N :
    ∀ c : ℝ, c < 1 →
      ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          (g k N : ℝ) > (N : ℝ) ^ c := by
  intro c hc
  have hε : 1 - c > 0 := by linarith
  obtain ⟨k₀, hk₀⟩ := general_lower_bound (1 - c) hε
  exact ⟨k₀, hk₀⟩

/-! ## Part VIII: The Odd Numbers Construction -/

/-- The set of odd numbers in {1,...,2N}. -/
def oddNumbers (N : ℕ) : Finset ℕ :=
  (Interval N).filter (fun n => n % 2 = 1)

/-- The odd numbers have cardinality exactly N. -/
theorem oddNumbers_card (N : ℕ) : (oddNumbers N).card = N := by
  sorry

/-- For odd numbers, no b₁, b₂, b₃ have all pairwise sums odd.
    (If b₁, b₂ have the same parity, their sum is even.) -/
theorem oddNumbers_no_triple (N : ℕ) :
    ¬∃ b : Fin 3 → ℤ, HasAllPairwiseSums (oddNumbers N) b := by
  intro ⟨b, hb⟩
  -- Among b₀, b₁, b₂, at least two have the same parity
  -- Their sum is even, contradiction
  sorry

/-- This shows g₃(N) ≥ 1 (actually ≥ 2 with more care). -/
theorem g3_ge_1 (N : ℕ) (hN : N ≥ 1) : g 3 N ≥ 1 := by
  sorry

/-! ## Part IX: Summary Table -/

/-- **Summary of Known Bounds for g_k(N)**

| k | Lower Bound | Upper Bound | Status |
|---|-------------|-------------|--------|
| 3 | 2 | 2 | EXACT |
| 4 | ? | 2032 | BOUNDED |
| 5 | c₁ log N | c₂ log N | ASYMPTOTIC |
| 6 | c₁ √N | c₂ √N | ASYMPTOTIC |
| k | N^{1-ε} (large k) | N^{1-2^{-k}} | GAP |

The gap between bounds widens as k increases. -/
theorem summary_g3 : ∀ N ≥ 1, g 3 N = 2 := g3_exact
theorem summary_g4 : ∃ C, ∀ N ≥ 1, g 4 N ≤ C := g4_bounded
theorem summary_g5 : ∃ c₁ c₂ > 0, ∃ N₀, ∀ N ≥ N₀,
    c₁ * N.log ≤ g 5 N ∧ (g 5 N : ℝ) ≤ c₂ * N.log := g5_asymptotic
theorem summary_g6 : ∃ c₁ c₂ > 0, ∃ N₀, ∀ N ≥ N₀,
    c₁ * (N : ℝ).sqrt ≤ g 6 N ∧ (g 6 N : ℝ) ≤ c₂ * (N : ℝ).sqrt := g6_asymptotic

/-! ## Part X: Open Problems -/

/-- **Open Problem 1:** Determine g₄(N) exactly.

    Known: 0 ≤ g₄(N) ≤ 2032. Is g₄(N) constant? What is its value? -/
def openProblem_g4_exact : Prop :=
  ∃ c : ℕ, ∀ N : ℕ, N ≥ 1 → g 4 N = c

/-- **Open Problem 2:** Determine constants in g₅(N) ≍ log N.

    What are the optimal c₁, c₂ with c₁ log N ≤ g₅(N) ≤ c₂ log N? -/
def openProblem_g5_constants : Prop :=
  -- Find optimal constants
  True

/-- **Open Problem 3:** Close the gap for large k.

    Upper: g_k(N) ≪ N^{1-2^{-k}}
    Lower: g_k(N) ≫ N^{1-ε} for any ε > 0 (large k)

    These don't match - can we close the gap? -/
def openProblem_large_k_gap : Prop :=
  -- Find matching bounds for general k
  True

/-- **Open Problem 4:** Structural characterization.

    For which sets A is the pairwise sums condition avoided?
    What structure do extremal sets have? -/
def openProblem_extremal_structure : Prop :=
  -- Characterize extremal sets
  True

/-! ## Part XI: The Main Summary -/

/--
**Summary of Erdős Problem #866**

**Problem**: For k ≥ 3, define g_k(N) as the minimal threshold such that
any A ⊆ {1,...,2N} with |A| ≥ N + g_k(N) contains all pairwise sums
of some b₁,...,b_k.

**Known Results**:
1. g₃(N) = 2 (exact)
2. g₄(N) ≤ 2032 (bounded constant)
3. g₅(N) ≍ log N (logarithmic growth)
4. g₆(N) ≍ √N (square root growth)
5. g_k(N) ≪_k N^{1-2^{-k}} (general upper bound)
6. g_k(N) > N^{1-ε} for large k (nearly linear lower bound)

**Status**: PARTIALLY SOLVED
- Small k (3,4,5,6): Well understood
- Large k: Gap between bounds

**Key Construction**: Odd numbers + powers of 2 avoid the condition

**Significance**: Connects additive combinatorics to threshold phenomena
-/
theorem erdos_866_summary : True := trivial

end Erdos866
