import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Sum of Reciprocal Odd Squares: ∑ 1/(2k+1)² = π²/8

## What This Proves
Restricting the Basel sum ∑ 1/n² = π²/6 to the **odd** integers gives

  ∑_{k=0}^∞ 1/(2k+1)² = π²/8.

## Approach
This is an elementary corollary of the Basel identity (`hasSum_zeta_two`).
Split the full sum over ℕ into its even- and odd-indexed subsequences using
`HasSum.even_add_odd`:

  ∑_{n} 1/n²  =  ∑_{k} 1/(2k)²  +  ∑_{k} 1/(2k+1)².

The even part rescales the original series:

  ∑_{k} 1/(2k)² = (1/4) ∑_{k} 1/k² = (1/4)·(π²/6) = π²/24.

Both the even part and the full sum have known values, so by uniqueness of
infinite sums the odd part must equal

  π²/6 − π²/24 = π²/8.

No new analysis is required beyond Mathlib's `hasSum_zeta_two`; the content is
the even/odd decomposition and the arithmetic identity 6 = 24 − ... that pins
the odd tail. The companion identity ∑ 1/(2k)² = π²/24 (sum of reciprocal even
squares) falls out of the same decomposition and is recorded as well.

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Uses Mathlib for the underlying Basel identity

## Mathlib Dependencies
- `hasSum_zeta_two` : the Basel identity ∑ 1/n² = π²/6
- `HasSum.even_add_odd` : splits a `HasSum` over ℕ into even/odd subsequences
- `HasSum.mul_left`, `HasSum.unique`

Original formalization for Lean Genius.
-/

namespace BaselProblemOQ06OQ01

open Filter Topology Real

/-- The base summand `f n = 1/n²`. -/
private noncomputable def f (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2

/-- **Basel identity** (Mathlib): `∑ 1/n² = π²/6`. -/
theorem basel_hasSum : HasSum f (π ^ 2 / 6) := hasSum_zeta_two

/-- **Sum of reciprocal even squares**: `∑_{k} 1/(2k)² = π²/24`.

Each even-indexed term is `1/(2k)² = (1/4)·(1/k²)`, so the even subsequence is
the original Basel series scaled by `1/4`, giving `(1/4)·(π²/6) = π²/24`. -/
theorem hasSum_even : HasSum (fun k : ℕ => f (2 * k)) (π ^ 2 / 24) := by
  have h : HasSum (fun n : ℕ => (1 / 4 : ℝ) * f n) ((1 / 4) * (π ^ 2 / 6)) :=
    basel_hasSum.mul_left (1 / 4)
  have hval : (1 / 4 : ℝ) * (π ^ 2 / 6) = π ^ 2 / 24 := by ring
  rw [hval] at h
  refine h.congr_fun ?_  -- reduce to a pointwise function identity
  intro k
  show f (2 * k) = (1 / 4 : ℝ) * f k
  unfold f
  push_cast
  rw [show (2 * (k : ℝ)) ^ 2 = 4 * (k : ℝ) ^ 2 from by ring, one_div_mul_one_div]

/-- The odd subsequence `k ↦ 1/(2k+1)²` is summable (a subseries of a summable
nonnegative series). -/
theorem summable_odd : Summable (fun k : ℕ => f (2 * k + 1)) := by
  have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    -- `hab : (fun k => 2*k+1) a = (fun k => 2*k+1) b`; coerce to the beta-reduced
    -- arithmetic equation (defeq) so `omega` can see through the lambda.
    have hab' : 2 * a + 1 = 2 * b + 1 := hab
    omega
  exact basel_hasSum.summable.comp_injective hi

/-- **Sum of reciprocal odd squares**: `∑_{k} 1/(2k+1)² = π²/8`.

The even part (π²/24) plus the odd part recovers the full Basel sum (π²/6), so
the odd part equals `π²/6 − π²/24 = π²/8`. -/
theorem hasSum_odd : HasSum (fun k : ℕ => f (2 * k + 1)) (π ^ 2 / 8) := by
  -- Let `b` be the (a priori unknown) value of the odd sum.
  obtain ⟨b, hb⟩ := summable_odd
  -- Even + odd reconstructs the whole series.
  have hcombined : HasSum f (π ^ 2 / 24 + b) := hasSum_even.even_add_odd hb
  -- Uniqueness against the Basel value pins `b`.
  have heq : π ^ 2 / 6 = π ^ 2 / 24 + b := basel_hasSum.unique hcombined
  have hb_val : b = π ^ 2 / 8 := by linarith
  rwa [hb_val] at hb

/-- **Main theorem** in the natural `(2k+1 : ℝ)` form:
`∑_{k=0}^∞ 1/(2k+1)² = π²/8`. -/
theorem odd_squares_hasSum :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  have h := hasSum_odd
  refine h.congr_fun ?_
  intro k
  show 1 / (2 * (k : ℝ) + 1) ^ 2 = f (2 * k + 1)
  unfold f
  push_cast
  ring

/-- The `tsum` form: `∑' k, 1/(2k+1)² = π²/8`. -/
theorem odd_squares_tsum :
    ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 2 = π ^ 2 / 8 :=
  odd_squares_hasSum.tsum_eq

/-- Sanity check: the odd-square sum is positive. -/
theorem odd_squares_pos : (0 : ℝ) < π ^ 2 / 8 := by positivity

/-- Consistency: even part + odd part = full Basel sum. -/
theorem even_add_odd_eq_basel : π ^ 2 / 24 + π ^ 2 / 8 = π ^ 2 / 6 := by ring

end BaselProblemOQ06OQ01
