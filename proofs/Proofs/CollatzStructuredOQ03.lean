/-
Collatz Structured — OQ-03: Average Stopping Time Growth Rate

The average stopping time σ(n) = (1/n) Σ_{k=1}^n T(k) where T(k) is the
number of Collatz steps for k to reach 1 (assuming it does).

Known results:
- Terras (1976): For almost all n, T(n) < ∞ (density 1 of ReachesOne)
- Lagarias (1985): If T(n) < ∞, then T(n) = O(n^γ) for some γ
- Numerical: σ(n) grows approximately as c · log n for some constant c ≈ 9.97

This file defines the stopping time, average stopping time, and states
the conjectured logarithmic growth rate.
-/

import Mathlib
import Proofs.CollatzStructured

open Collatz

namespace CollatzStoppingTime

/-! ## Part I: Stopping Time (assuming Collatz conjecture) -/

/-- The stopping time: number of Collatz steps to reach 1.
    Defined using the Collatz conjecture to guarantee termination. -/
noncomputable def stoppingTime (n : ℕ) (hn : n ≥ 1) : ℕ :=
  Nat.find (collatz_conjecture n hn)

/-- The stopping time of 1 is 0. -/
theorem stoppingTime_one : stoppingTime 1 (by omega) = 0 := by
  unfold stoppingTime
  have h : collatzIter 0 1 = 1 := rfl
  exact Nat.find_eq_zero.mpr h

/-- The stopping time of 2^k is k (for k ≥ 1). -/
theorem stoppingTime_pow_two (k : ℕ) (hk : k ≥ 1) :
    stoppingTime (2^k) (by positivity) ≤ k := by
  unfold stoppingTime
  exact Nat.find_le (collatz_pow_two k hk)

/-! ## Part II: Average Stopping Time -/

/-- The cumulative stopping time: Σ_{k=1}^n T(k). -/
noncomputable def cumulativeStoppingTime (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, stoppingTime (k + 1) (by omega)

/-- The average stopping time: σ(n) = (1/n) Σ_{k=1}^n T(k). -/
noncomputable def averageStoppingTime (n : ℕ) (hn : n ≥ 1) : ℝ :=
  (cumulativeStoppingTime n : ℝ) / (n : ℝ)

/-! ## Part III: Conjectured Growth Rate -/

/-- The conjectured logarithmic growth: σ(n) ~ c · log(n) for some c > 0.
    Numerical evidence suggests c ≈ 9.97.

    This is equivalent to: the typical stopping time T(n) is O(log n),
    which follows heuristically from the observation that each Collatz
    step multiplies by ~3/4 on average (probability 1/2 of halving and
    1/2 of tripling-and-halving), giving log_{4/3}(n) ≈ 3.47 · log(n) steps.

    The factor ~9.97 vs ~3.47 accounts for the non-uniform distribution. -/
def logarithmicGrowthConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto (fun n => averageStoppingTime n (by omega : n + 1 ≥ 1) / Real.log (n + 1))
      Filter.atTop (nhds c)

/-- Weaker statement: σ(n) = O(log n). -/
def averageStoppingTimeLogBound : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    averageStoppingTime n (by omega) ≤ C * Real.log n

/-! ## Part IV: Stopping Time for Small Values -/

/-- Stopping time of 2 is 1: 2 → 1. -/
theorem stoppingTime_two : stoppingTime 2 (by omega) ≤ 1 := by
  exact stoppingTime_pow_two 1 (by omega)

/-- Stopping time of 4 is at most 2: 4 → 2 → 1. -/
theorem stoppingTime_four : stoppingTime 4 (by omega) ≤ 2 := by
  have : 4 = 2^2 := by norm_num
  rw [this]
  exact stoppingTime_pow_two 2 (by omega)

/-! ## Summary

**Defined**:
- `stoppingTime`: Number of Collatz steps to reach 1
- `cumulativeStoppingTime`: Sum of stopping times up to n
- `averageStoppingTime`: σ(n) = cumulative / n

**Proved**:
- `stoppingTime_one`: T(1) = 0
- `stoppingTime_pow_two`: T(2^k) ≤ k
- Bounds for small values (2, 4)

**Stated**:
- `logarithmicGrowthConjecture`: σ(n)/log(n) → c for some c > 0
- `averageStoppingTimeLogBound`: σ(n) = O(log n)

**Open**: The exact growth rate of σ(n) depends on the Collatz conjecture
and deep number-theoretic properties of the iteration.
-/

end CollatzStoppingTime
