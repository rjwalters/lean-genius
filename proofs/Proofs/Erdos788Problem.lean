/-
Erdős Problem #788: Sum-Free Subsets in Intervals

Source: https://erdosproblems.com/788
Status: OPEN

Statement:
Let f(n) be maximal such that if B ⊂ (2n,4n) ∩ ℕ, there exists C ⊂ (n,2n) ∩ ℕ
such that c₁ + c₂ ∉ B for all c₁ ≠ c₂ ∈ C and |C| + |B| ≥ f(n).

Estimate f(n). Is it true that f(n) ≤ n^{1/2+o(1)}?

Background:
This is about sum-free subsets within specific intervals. Given any
set B in (2n, 4n), we seek a set C in (n, 2n) such that no two
distinct elements of C sum to something in B.

Key Results:
- Choi (1971): Conjectured the problem, proved f(n) ≪ n^{3/4}
- Adenwalla: Proved f(n) ≫ n^{1/2} (via Sidon sets)
- Hunter: Improved to f(n) ≪ n^{2/3+o(1)}
- Baltz-Schoen-Srivastav (2000): Proved f(n) ≪ (n log n)^{2/3}

The gap between n^{1/2} and (n log n)^{2/3} remains open.

References:
- [Ch71] Choi, "On a combinatorial problem in number theory", 1971
- [BSS00] Baltz-Schoen-Srivastav, "Probabilistic construction of small
         strongly sum-free sets via large Sidon sets", 2000

Tags: additive-combinatorics, sum-free-sets, intervals
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

namespace Erdos788

/- ## Part I: Basic Definitions -/

/-- The set (a, b) ∩ ℕ: natural numbers strictly between a and b -/
def openInterval (a b : ℕ) : Finset ℕ :=
  (Finset.range b).filter (fun x => a < x ∧ x < b)

/-- The interval (n, 2n) ∩ ℕ -/
def lowerInterval (n : ℕ) : Finset ℕ := openInterval n (2 * n)

/-- The interval (2n, 4n) ∩ ℕ -/
def upperInterval (n : ℕ) : Finset ℕ := openInterval (2 * n) (4 * n)

/-- The set of pairwise sums {c₁ + c₂ : c₁ ≠ c₂ ∈ C} -/
def pairwiseSums (C : Finset ℕ) : Finset ℕ :=
  (C.product C).filter (fun p => p.1 ≠ p.2) |>.image (fun p => p.1 + p.2)

/-- C is sum-free with respect to B: no two distinct elements of C sum into B -/
def isSumFreeWithResp (C B : Finset ℕ) : Prop :=
  ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → c₁ + c₂ ∉ B

/-- Equivalent: C is sum-free w.r.t. B iff pairwiseSums(C) and B are disjoint -/
/- ## Part II: The Function f(n) -/

/-- A pair (B, C) is valid: B ⊂ (2n,4n), C ⊂ (n,2n), C sum-free w.r.t. B -/
def isValidConfig (n : ℕ) (B C : Finset ℕ) : Prop :=
  B ⊆ upperInterval n ∧
  C ⊆ lowerInterval n ∧
  isSumFreeWithResp C B

/-- f(n) is the maximum value such that for all B ⊂ (2n, 4n), there exists
C ⊂ (n, 2n) sum-free w.r.t. B with |C| + |B| ≥ f(n). Axiomatized since
computing this requires deep combinatorial arguments. -/
axiom f (n : ℕ) : ℕ

/- ## Part III: Choi's Bound and Conjecture (1971) -/

/-- Choi (1971): f(n) ≪ n^{3/4} -/
/-- Choi's conjecture: f(n) ≤ n^{1/2+o(1)} (OPEN) -/
def choiConjecture : Prop :=
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, (f n : ℝ) ≤ (n : ℝ) ^ (1/2 + ε : ℝ)

/- ## Part IV: Adenwalla's Lower Bound -/

/-- Adenwalla: f(n) ≫ n^{1/2}, proved by taking C to be a Sidon set.
A Sidon set has all pairwise sums distinct, giving control over which
elements of (2n, 4n) are hit. -/
axiom adenwalla_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≥ c * (n : ℝ) ^ (1/2 : ℝ)

/-- A Sidon set (B₂ set): all pairwise sums a + b (a ≤ b) are distinct -/
def isSidonSet (S : Finset ℕ) : Prop :=
  ∀ a₁ b₁ a₂ b₂, a₁ ∈ S → b₁ ∈ S → a₂ ∈ S → b₂ ∈ S →
    a₁ ≤ b₁ → a₂ ≤ b₂ → a₁ + b₁ = a₂ + b₂ → (a₁ = a₂ ∧ b₁ = b₂)

/-- There exist Sidon sets of size ~√n in any interval of length n -/
/- ## Part V: Hunter's and BSS Improvements -/

/-- Hunter: f(n) ≪ n^{2/3+o(1)}, improving Choi's 3/4 exponent -/
/-- Baltz-Schoen-Srivastav (2000): best known upper bound
f(n) ≪ (n log n)^{2/3}, using probabilistic construction
of large Sidon sets. -/
axiom bss_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (f n : ℝ) ≤ C * ((n : ℝ) * Real.log n) ^ (2/3 : ℝ)

/- ## Part VI: Interval Arithmetic -/

/-- Sums from (n, 2n) land in (2n, 4n): for c₁, c₂ ∈ (n, 2n) with c₁ ≠ c₂,
their sum is in (2n, 4n) (or outside the interval). -/
theorem interval_sum_range : ∀ n : ℕ, n ≥ 1 →
    ∀ c₁ ∈ lowerInterval n, ∀ c₂ ∈ lowerInterval n,
    c₁ ≠ c₂ → c₁ + c₂ ∈ upperInterval n ∨ c₁ + c₂ ≤ 2 * n ∨ c₁ + c₂ ≥ 4 * n := by
  intro n _ c₁ _ c₂ _ _
  by_cases h : c₁ + c₂ ∈ upperInterval n
  · left; exact h
  · right
    simp only [upperInterval, openInterval, mem_filter, mem_range] at h
    push_neg at h
    rcases h with h | h | h
    · right; omega
    · left; omega
    · right; omega

/-- Sums of distinct elements from (n, 2n) lie in (2n, 4n) -/
theorem sums_in_upper_interval : ∀ n : ℕ, n ≥ 1 →
    ∀ c₁ ∈ lowerInterval n, ∀ c₂ ∈ lowerInterval n,
    c₁ ≠ c₂ → c₁ + c₂ ∈ upperInterval n := by
  intro n _hn c₁ hc₁ c₂ hc₂ _hne
  simp only [lowerInterval, upperInterval, openInterval, mem_filter, mem_range] at *
  constructor
  · omega
  · constructor <;> omega

/- ## Part VII: Summary -/

/--
**Erdős Problem #788: Summary (OPEN)**

Current bounds: n^{1/2} ≪ f(n) ≪ (n log n)^{2/3}.
Choi's conjecture f(n) ≤ n^{1/2+o(1)} remains open.
The formalization captures the lower bound (Adenwalla via Sidon sets)
and the upper bound (Baltz-Schoen-Srivastav 2000).
-/
theorem erdos_788_summary :
    -- Lower bound: f(n) ≫ n^{1/2}
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≥ c * (n : ℝ) ^ (1/2 : ℝ)) ∧
    -- Upper bound: f(n) ≪ (n log n)^{2/3}
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f n : ℝ) ≤ C * ((n : ℝ) * Real.log n) ^ (2/3 : ℝ)) :=
  ⟨adenwalla_lower_bound, bss_bound⟩

end Erdos788
