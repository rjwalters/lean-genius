import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-
# The Negative Binomial Series: ∑ (n+k choose k) rⁿ = 1/(1-r)^{k+1}

## What This Proves

For a real ratio `r` with `‖r‖ < 1` and any fixed order `k : ℕ`,

  ∑_{n=0}^{∞} (n+k choose k) · rⁿ  =  1 / (1-r)^{k+1}.

This is the **negative binomial series** (also called the *generalized geometric
series* or the *(k+1)-fold self-convolution* of the geometric series).  It is the
common parent of the whole geometric-moment family already in the gallery:

  k = 0 : ∑ rⁿ              = 1/(1-r)     (the geometric series itself)
  k = 1 : ∑ (n+1) rⁿ        = 1/(1-r)²
  k = 2 : ∑ (n+2 choose 2) rⁿ = 1/(1-r)³
  ...

Differentiating `1/(1-r)` term-by-term `k` times, or convolving the geometric
series with itself `k+1` times, produces exactly these coefficients.  The
individual moments `∑ nᵐ rⁿ` (`GeometricSeriesOQ07`, `GeometricSeriesOQ10`) are
finite linear combinations of these members.

## Why This Is Worth Formalising

Mathlib packages the core analytic fact as
`hasSum_choose_mul_geometric_of_norm_lt_one`.  The contribution of this file is to
present that member as the **negative binomial series** and to expose the three
faces of its coefficient `(n+k choose k)` that make it more than a single lemma:

1. **Symmetric form** `(n+k choose k) = (n+k choose n)` — the two conventions in
   which the series appears in the literature.
2. **Stars-and-bars / multichoose form**
   `(n+k choose k) = multichoose (k+1) n`, i.e. the coefficient of `rⁿ` counts the
   monomials of degree `n` in `k+1` variables (equivalently, size-`n` multisets
   from a `(k+1)`-element set).  This is the combinatorial reason a
   `(k+1)`-fold product of geometric series has these coefficients: expanding
   `(∑ rⁿ)^{k+1}` and collecting the degree-`n` term counts weak compositions of
   `n` into `k+1` parts, of which there are `multichoose (k+1) n`.
3. **Moment-family bridges** to `k = 0` (recovering the geometric series) and
   `k = 1` (the first-moment-style series `∑ (n+1) rⁿ = 1/(1-r)²`).

## Status: 0 sorries, 0 axioms
-/

open Filter Topology

namespace GeometricSeriesOQ11

variable {r : ℝ}

/-! ## The negative binomial series -/

/-- **Negative binomial series** (`HasSum` form): for `‖r‖ < 1`,
`∑ (n+k choose k) rⁿ = 1/(1-r)^{k+1}`.

This is Mathlib's `hasSum_choose_mul_geometric_of_norm_lt_one`, specialised to `ℝ`
and named for the identity it expresses. -/
theorem hasSum_negBinomial (k : ℕ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => ((n + k).choose k : ℝ) * r ^ n) (1 / (1 - r) ^ (k + 1)) :=
  hasSum_choose_mul_geometric_of_norm_lt_one k hr

/-- **Negative binomial series** (`tsum` form). -/
theorem tsum_negBinomial (k : ℕ) (hr : ‖r‖ < 1) :
    ∑' n : ℕ, ((n + k).choose k : ℝ) * r ^ n = 1 / (1 - r) ^ (k + 1) :=
  (hasSum_negBinomial k hr).tsum_eq

/-- The negative binomial series is summable. -/
theorem summable_negBinomial (k : ℕ) (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n + k).choose k : ℝ) * r ^ n) :=
  (hasSum_negBinomial k hr).summable

/-- Restatement with the real-analysis hypothesis `|r| < 1` (equivalent to `‖r‖ < 1`
over `ℝ`), the form in which the series is usually quoted. -/
theorem hasSum_negBinomial_of_abs_lt_one (k : ℕ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => ((n + k).choose k : ℝ) * r ^ n) (1 / (1 - r) ^ (k + 1)) :=
  hasSum_negBinomial k (by rwa [Real.norm_eq_abs])

/-! ## Symmetric coefficient form -/

/-- Pascal symmetry across the two standard conventions:
`(n+k choose n) = (n+k choose k)`. -/
lemma choose_symm_add (n k : ℕ) : (n + k).choose n = (n + k).choose k := by
  have h : k ≤ n + k := Nat.le_add_left k n
  rw [← Nat.choose_symm h, Nat.add_sub_cancel]

/-- **Symmetric form** of the series: `∑ (n+k choose n) rⁿ = 1/(1-r)^{k+1}`. -/
theorem hasSum_negBinomial' (k : ℕ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => ((n + k).choose n : ℝ) * r ^ n) (1 / (1 - r) ^ (k + 1)) := by
  have hfun : (fun n : ℕ => ((n + k).choose n : ℝ) * r ^ n)
      = (fun n : ℕ => ((n + k).choose k : ℝ) * r ^ n) := by
    funext n; rw [choose_symm_add]
  rw [hfun]; exact hasSum_negBinomial k hr

/-! ## Stars-and-bars (multichoose) form -/

/-- The coefficient equals a multiset coefficient:
`(n+k choose k) = multichoose (k+1) n`, the number of size-`n` multisets drawn from
a `(k+1)`-element set (equivalently, monomials of degree `n` in `k+1` variables). -/
lemma choose_add_eq_multichoose (n k : ℕ) :
    (n + k).choose k = Nat.multichoose (k + 1) n := by
  rw [Nat.multichoose_eq, show k + 1 + n - 1 = n + k by omega]
  exact (choose_symm_add n k).symm

/-- **Stars-and-bars form**: `∑ (multichoose (k+1) n) rⁿ = 1/(1-r)^{k+1}`.

Read the right-hand side as `(∑ rⁿ)^{k+1}`: the degree-`n` coefficient of the
`(k+1)`-fold product of the geometric series counts weak compositions of `n` into
`k+1` parts, of which there are `multichoose (k+1) n`. -/
theorem hasSum_multichoose (k : ℕ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => (Nat.multichoose (k + 1) n : ℝ) * r ^ n) (1 / (1 - r) ^ (k + 1)) := by
  have hfun : (fun n : ℕ => (Nat.multichoose (k + 1) n : ℝ) * r ^ n)
      = (fun n : ℕ => ((n + k).choose k : ℝ) * r ^ n) := by
    funext n; rw [← choose_add_eq_multichoose]
  rw [hfun]; exact hasSum_negBinomial k hr

/-! ## Bridges to the geometric-moment family -/

/-- **`k = 0` bridge**: the negative binomial series specialises to the geometric
series `∑ rⁿ = 1/(1-r)`. -/
theorem hasSum_geometric (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => r ^ n) (1 / (1 - r)) := by
  have h := hasSum_negBinomial 0 hr
  simpa using h

/-- **`k = 1` bridge**: `∑ (n+1) rⁿ = 1/(1-r)²`. -/
theorem hasSum_succ_mul_geometric (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) (1 / (1 - r) ^ 2) := by
  have h := hasSum_negBinomial 1 hr
  have hfun : (fun n : ℕ => ((n + 1).choose 1 : ℝ) * r ^ n)
      = (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
    funext n; rw [Nat.choose_one_right]; push_cast; ring
  rw [hfun] at h
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  exact h

/-! ## A concrete value -/

/-- Sanity check at `r = 1/2`, order `k = 2`: `∑ (n+2 choose 2)/2ⁿ = 8`.
(`1/(1-1/2)³ = 1/(1/2)³ = 8`.) -/
example : ∑' n : ℕ, ((n + 2).choose 2 : ℝ) * (1 / 2 : ℝ) ^ n = 8 := by
  rw [tsum_negBinomial 2 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

end GeometricSeriesOQ11
