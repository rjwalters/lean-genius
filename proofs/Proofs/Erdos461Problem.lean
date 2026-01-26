/-!
# Erdős Problem 461: Distinct Smooth Components in Short Intervals

Let `sₜ(n)` be the `t`-smooth component of `n`, i.e., the largest divisor
of `n` whose prime factors are all less than `t`. Define `f(n, t)` as the
number of distinct values of `sₜ(m)` for `m ∈ {n+1, …, n+t}`.

Is `f(n, t) ≫ t` for all `n` and `t`?

Erdős and Graham proved the weaker bound `f(n, t) ≫ t / log t`.

*Reference:* [erdosproblems.com/461](https://www.erdosproblems.com/461),
Erdős–Graham (1980), p. 92.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Smooth components -/

/-- The `t`-smooth component of `n`: the largest divisor of `n` all of
whose prime factors are strictly less than `t`. -/
noncomputable def smoothComponent (t n : ℕ) : ℕ :=
    (n.factors.filter (· < t)).foldl (· * ·) 1

/-- `smoothComponent t n` always divides `n`. -/
axiom smoothComponent_dvd (t n : ℕ) : smoothComponent t n ∣ n

/-- `smoothComponent t n` is `t`-smooth: every prime factor is `< t`. -/
axiom smoothComponent_smooth (t n : ℕ) (p : ℕ) :
    p.Prime → p ∣ smoothComponent t n → p < t

/-- `smoothComponent t n` is the largest such divisor. -/
axiom smoothComponent_largest (t n d : ℕ) :
    d ∣ n → (∀ p : ℕ, p.Prime → p ∣ d → p < t) → d ∣ smoothComponent t n

/-! ## Counting distinct smooth components -/

/-- `f(n, t)` counts the distinct values of `sₜ(m)` for `m ∈ {n+1, …, n+t}`. -/
noncomputable def smoothDistinctCount (n t : ℕ) : ℕ :=
    ((Finset.Icc (n + 1) (n + t)).image (smoothComponent t)).card

/-! ## Main conjecture -/

/-- Erdős Problem 461: There exists `C > 0` such that `f(n, t) ≥ C · t`
for all `n` and sufficiently large `t`. -/
def ErdosProblem461 : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        ∀ n : ℕ, C * (t : ℝ) ≤ (smoothDistinctCount n t : ℝ)

/-! ## Known results -/

/-- Erdős–Graham: `f(n, t) ≫ t / log t`. -/
axiom erdos_graham_lower :
    ∃ C : ℝ, 0 < C ∧
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        ∀ n : ℕ, C * (t : ℝ) / Real.log (t : ℝ) ≤ (smoothDistinctCount n t : ℝ)

/-! ## Basic properties -/

/-- The smooth component of 1 is always 1. -/
axiom smoothComponent_one (t : ℕ) : smoothComponent t 1 = 1

/-- For `t = 1`, every smooth component is 1 (no primes below 1). -/
axiom smoothComponent_t_one (n : ℕ) : smoothComponent 1 n = 1

/-- The count is at most `t` (there are only `t` values in the interval). -/
axiom smoothDistinctCount_le (n t : ℕ) : smoothDistinctCount n t ≤ t

/-- For `t = 0`, the interval is empty, so the count is 0. -/
axiom smoothDistinctCount_zero (n : ℕ) : smoothDistinctCount n 0 = 0
