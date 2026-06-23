import Mathlib
import Proofs.LagrangeFourSquaresWaringG2OQ03OQ05OQ01

/-!
# The normalized one-sided density error converges to `4` along the extremal family

**Open question (`lagrange-four-squares-waring-g2-oq-03-oq-05-oq-01-oq-01`)**, the first
follow-up left by `oq-03-oq-05-oq-01` (*"the non-three-square density error is one-sided and
genuinely unbounded"*).

Recall the setting.  The integers **not** representable as a sum of three squares form the
excluded family `E = { 4^a (8b+7) }` (Legendre), with counting function
`excludedCount N = #{ n < N : n ∈ E }`.  The sibling `oq-03-oq-05` proved the density law
`excludedCount N / N → 1/6`, and `oq-03-oq-05-oq-01` analysed the error
`E(N) = N − 6·excludedCount N`, showing it is one-sided (`E(N) ≥ 0` always) and unbounded
above via the **extremal family** `a 0 = 6`, `a (k+1) = 4·a k − 2` (closed form
`a k = (4^{k+2}+2)/3`), along which the error is *exactly*

  `E(a k) = 4k + 6`   (`error_eq`).

That entry observed that `a k ≈ 4^k`, so the error is `Θ(log N)`, and asked for the precise
**normalized extremal constant**: does `E(a k) / log₄(a k) → 4`?

## What is new here

This file proves that limit.  The whole computation is a squeeze: from the exact closed form
`3·a k = 4^{k+2}+2` one gets the elementary two-sided bound

  `(k+2) − log₄ 3  ≤  log₄(a k)  ≤  k+2`,

while the numerator is the exact value `E(a k) = 4k+6`.  Hence

  `E(a k) / log₄(a k)  =  (4k+6) / log₄(a k)  ⟶  4`   (`normalized_error_tendsto_four`),

because both the `(4k+6)/(k+2)` lower comparison and the `(4k+6)/((k+2)−log₄3)` upper
comparison tend to `4`.  Concretely we show `|E(a k)/log₄(a k) − 4| ≤ (2 + 4·log₄3)/log₄(a k)`
and let `log₄(a k) → ∞`.

This pins the normalized constant of the explicit extremal subsequence to exactly `4`.  Whether
`4` is also the true `limsup` of the normalized one-sided error over *all* `N` — i.e. whether
some other residue chain or interleaving of descents pushes the constant strictly above `4` —
is a separate question not settled here.  All proofs are axiom-free and reuse the parent's
`error_eq` and extremal family `a` verbatim.
-/

open Filter Topology

open LagrangeFourSquaresWaringG2OQ03OQ05
open LagrangeFourSquaresWaringG2OQ03OQ05OQ01

namespace LagrangeFourSquaresWaringG2OQ03OQ05OQ01OQ01

/-! ## The closed form `3·a k = 4^{k+2}+2` and real-number bounds -/

/-- **Closed form (integer shape):** `3·a k = 4^{k+2}+2`.  Proved by induction from the
recurrence `a (k+1) = 4·a k − 2`; the `ℕ`-subtraction is safe because `a k ≥ 6`. -/
theorem three_mul_a (k : ℕ) : 3 * a k = 4 ^ (k + 2) + 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hstep : a (k + 1) = 4 * a k - 2 := rfl
    have hge := a_ge k
    have hpow : 4 ^ (k + 1 + 2) = 4 * 4 ^ (k + 2) := by
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]; ring
    omega

/-- **Closed form (real shape):** `a k = (4^{k+2}+2)/3` over `ℝ`. -/
theorem a_real (k : ℕ) : (a k : ℝ) = (4 ^ (k + 2) + 2) / 3 := by
  have h : (3 : ℝ) * (a k : ℝ) = 4 ^ (k + 2) + 2 := by exact_mod_cast three_mul_a k
  linarith

/-- Lower bound `4^{k+2}/3 ≤ a k`. -/
theorem a_lb (k : ℕ) : (4 : ℝ) ^ (k + 2) / 3 ≤ (a k : ℝ) := by
  rw [a_real]; linarith

/-- Upper bound `a k ≤ 4^{k+2}` (uses `1 ≤ 4^{k+2}`). -/
theorem a_ub (k : ℕ) : (a k : ℝ) ≤ (4 : ℝ) ^ (k + 2) := by
  have hX : (1 : ℝ) ≤ (4 : ℝ) ^ (k + 2) := by
    calc (1 : ℝ) = 1 ^ (k + 2) := (one_pow _).symm
      _ ≤ 4 ^ (k + 2) := by gcongr <;> norm_num
  rw [a_real]; linarith

/-- Positivity of `a k` over `ℝ`. -/
theorem a_pos (k : ℕ) : (0 : ℝ) < (a k : ℝ) := by
  have : (0 : ℕ) < a k := by have := a_ge k; omega
  exact_mod_cast this

/-! ## Two-sided bounds on `log₄(a k)` -/

/-- **Upper bound:** `log₄(a k) ≤ k+2`, since `a k ≤ 4^{k+2}` and `log₄(4^{k+2}) = k+2`. -/
theorem logb_a_ub (k : ℕ) : Real.logb 4 (a k) ≤ (k + 2 : ℝ) := by
  have h2 : Real.logb 4 (a k) ≤ Real.logb 4 ((4 : ℝ) ^ (k + 2)) :=
    Real.logb_le_logb_of_le (by norm_num) (a_pos k) (a_ub k)
  have h3 : Real.logb 4 ((4 : ℝ) ^ (k + 2)) = (k + 2 : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; push_cast; ring
  rw [h3] at h2; exact h2

/-- **Lower bound:** `(k+2) − log₄ 3 ≤ log₄(a k)`, since `4^{k+2}/3 ≤ a k` and
`log₄(4^{k+2}/3) = (k+2) − log₄ 3`. -/
theorem logb_a_lb (k : ℕ) : (k + 2 : ℝ) - Real.logb 4 3 ≤ Real.logb 4 (a k) := by
  have hpos : (0 : ℝ) < (4 : ℝ) ^ (k + 2) / 3 := by positivity
  have h2 : Real.logb 4 ((4 : ℝ) ^ (k + 2) / 3) ≤ Real.logb 4 (a k) :=
    Real.logb_le_logb_of_le (by norm_num) hpos (a_lb k)
  have h3 : Real.logb 4 ((4 : ℝ) ^ (k + 2) / 3) = (k + 2 : ℝ) - Real.logb 4 3 := by
    rw [Real.logb_div (by positivity).ne' (by norm_num), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  rw [h3] at h2; exact h2

/-- `log₄(a k) > 0` for every `k` (since `a k ≥ 6 > 1`). -/
theorem logb_a_pos (k : ℕ) : 0 < Real.logb 4 (a k) := by
  have h := a_ge k
  have h1 : (1 : ℝ) < (a k : ℝ) := by
    have : (1 : ℕ) < a k := by omega
    exact_mod_cast this
  exact Real.logb_pos (by norm_num) h1

/-! ## The numerator is the exact value `4k+6` -/

/-- The one-sided error along the family, as a real number: `a k − 6·excludedCount (a k) = 4k+6`.
This is the parent's `error_eq` pushed from `ℤ` to `ℝ`. -/
theorem error_real (k : ℕ) :
    (a k : ℝ) - 6 * (excludedCount (a k) : ℝ) = 4 * (k : ℝ) + 6 := by
  have h := error_eq k
  exact_mod_cast h

/-! ## The normalized error converges to `4` -/

/-- **Headline.**  Along the extremal family `a k = (4^{k+2}+2)/3`, the normalized one-sided
density error converges to exactly `4`:

  `(a k − 6·excludedCount (a k)) / log₄(a k) ⟶ 4`   as `k → ∞`.

The numerator is the exact value `4k+6` (`error_real`), the denominator is squeezed by
`(k+2) − log₄3 ≤ log₄(a k) ≤ k+2`, and `|error/log₄ − 4| ≤ (2 + 4·log₄3)/log₄(a k) → 0`. -/
theorem normalized_error_tendsto_four :
    Tendsto (fun k : ℕ => ((a k : ℝ) - 6 * (excludedCount (a k) : ℝ)) / Real.logb 4 (a k))
      atTop (nhds 4) := by
  have hlognn : (0 : ℝ) ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  -- `log₄ 3 ≤ 1`, since `3 ≤ 4` and `log₄ 4 = 1`
  have hlog3le1 : Real.logb 4 3 ≤ 1 := by
    have h := Real.logb_le_logb_of_le (b := 4) (by norm_num) (by norm_num) (by norm_num : (3 : ℝ) ≤ 4)
    rwa [Real.logb_self_eq_one (by norm_num)] at h
  -- the denominator tends to `+∞` (it dominates `k`, since `log₄(a k) ≥ (k+2) − log₄3 ≥ k`)
  have hlogtop : Tendsto (fun k : ℕ => Real.logb 4 (a k)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have := logb_a_lb k; linarith
  -- the error bound function tends to `0`
  have hbnd0 :
      Tendsto (fun k : ℕ => (2 + 4 * Real.logb 4 3) * (Real.logb 4 (a k))⁻¹) atTop (nhds 0) := by
    have hinv := hlogtop.inv_tendsto_atTop
    have := hinv.const_mul (2 + 4 * Real.logb 4 3)
    simpa using this
  -- lower and upper comparison functions, both tending to `4`
  have hc4 : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4) := tendsto_const_nhds
  have hg :
      Tendsto (fun k : ℕ => 4 - (2 + 4 * Real.logb 4 3) * (Real.logb 4 (a k))⁻¹)
        atTop (nhds 4) := by
    simpa using hc4.sub hbnd0
  have hh :
      Tendsto (fun k : ℕ => 4 + (2 + 4 * Real.logb 4 3) * (Real.logb 4 (a k))⁻¹)
        atTop (nhds 4) := by
    simpa using hc4.add hbnd0
  -- the squeeze bounds, established by clearing the positive denominator
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg hh (fun k => ?_) (fun k => ?_)
  · -- lower: `4 - (2+4·log₄3)/L ≤ (4k+6)/L`
    have hL := logb_a_pos k
    have hub := logb_a_ub k
    rw [error_real k, ← div_eq_mul_inv, sub_le_iff_le_add, div_add_div_same, le_div_iff₀ hL]
    linarith [hub, hlognn]
  · -- upper: `(4k+6)/L ≤ 4 + (2+4·log₄3)/L`
    have hL := logb_a_pos k
    have hlb := logb_a_lb k
    rw [error_real k, ← div_eq_mul_inv, ← sub_le_iff_le_add, div_sub_div_same, div_le_iff₀ hL]
    linarith [hlb, hlognn]

end LagrangeFourSquaresWaringG2OQ03OQ05OQ01OQ01
