/-
  Aristotle targets for Erdős Problem #1049
  Routine supporting lemmas for automated proof search.
  See Erdos1049Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT Chowla's conjecture or the open irrationality question
  - Known results: summability, series bounds, Lambert rewriting
  - Clean theorem statements with no definition sorries

  Excluded (deep/open results kept in main file):
  - S_eq_D (classical identity, medium difficulty — rearrangement argument)
  - double_sum_identity (related to S_eq_D)
  - S_at_2_first_terms (partial sum splitting)
  - S_tendsto_infinity (boundary limit analysis)
-/
import Mathlib

namespace Erdos1049.Aristotle

open BigOperators Nat Real Filter

/- Definitions mirrored from main file -/

def tau (n : ℕ) : ℕ := n.divisors.card

noncomputable def S (t : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (t ^ n - 1)

noncomputable def D (t : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else (tau n : ℝ) / t ^ n

noncomputable def isLambertSeries (f : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then (0 : ℝ) else f n * q^n / (1 - q^n)

/- ## Section 1: Summability -/

-- The series ∑ 1/(t^n - 1) converges for t > 1
-- Proof idea: for t > 1, t^n - 1 ≥ (t-1)t^{n-1}, so 1/(t^n-1) ≤ C/t^n
theorem S_summable (t : ℝ) (ht : t > 1) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else 1 / (t ^ n - 1)) := by sorry

-- The divisor series ∑ τ(n)/t^n converges for t > 1
-- Proof idea: τ(n) ≤ n, so τ(n)/t^n ≤ n/t^n, and ∑ n/t^n converges
theorem D_summable (t : ℝ) (ht : t > 1) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (tau n : ℝ) / t ^ n) := by sorry

/- ## Section 2: Limits -/

-- S(t) → 0 as t → +∞ (each term → 0 and dominated)
theorem S_tendsto_zero : Tendsto S atTop (nhds 0) := by sorry

/- ## Section 3: Bounds -/

-- Lower bound: S(t) ≥ 1/(t-1) (just the n=1 term: 1/(t-1))
-- Upper bound: S(t) ≤ t/(t-1)² (comparison with geometric series)
theorem S_bounds (t : ℝ) (ht : t > 1) :
    1 / (t - 1) ≤ S t ∧ S t ≤ t / (t - 1)^2 := by sorry

/- ## Section 4: Lambert Series Rewriting -/

-- S(t) equals the Lambert series with constant coefficients 1 and q = 1/t
-- This is a definitional rewriting: 1/(t^n - 1) = (1/t)^n / (1 - (1/t)^n)
theorem S_as_lambert (t : ℝ) (ht : t > 1) :
    S t = isLambertSeries (fun _ => 1) (1/t) := by sorry

end Erdos1049.Aristotle
