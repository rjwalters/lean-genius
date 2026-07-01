import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# The Negative-Binomial Series ∑ binom(n+k, k)·rⁿ = (1 − r)⁻⁽ᵏ⁺¹⁾ (geometric-series-oq-06-oq-02)

The parent entry (`geometric-series-oq-06`) obtains the arithmetico-geometric
series `∑' n, n·rⁿ = r/(1 − r)²` by differentiating the geometric series once.
Its open question asks:

  > Does the term-by-term differentiation generalize cleanly to
  > `∑ binom(n+k, k)·rⁿ = (1 − r)⁻⁽ᵏ⁺¹⁾` for all `k`, via Mathlib's
  > descending-factorial weighted geometric series?

**Answer: yes.**  Differentiating `∑ rⁿ = 1/(1 − r)` exactly `k` times (and dividing
by `k!`) produces the **negative-binomial series**

    ∑' n, binom(n+k, k) · rⁿ = 1 / (1 − r)^(k+1)      (‖r‖ < 1),

whose coefficients `binom(n+k, k)` count the weak compositions of `n` into `k+1`
parts — the generating function `(1 − r)^{-(k+1)}` of the negative-binomial
distribution.  Mathlib packages exactly this identity as
`hasSum_choose_mul_geometric_of_norm_lt_one`, so the generalization is available
off the shelf and this file records the answer, ties it back to the parent, and
verifies the promised specializations.

What this file adds on top of the raw Mathlib lemma:

* the whole `k`-indexed family in `HasSum` / `Summable` / `tsum` form;
* the two anchoring specializations `k = 0` (geometric series `1/(1 − r)`) and
  `k = 1` (shifted companion `∑ (n+1)·rⁿ = 1/(1 − r)²`);
* a **closed loop back to the parent**: the arithmetico-geometric first moment
  `∑' n, n·rⁿ = r/(1 − r)²` is re-derived as the `k = 1` family minus the `k = 0`
  family, exhibiting the parent's result as a genuine special case of the
  generalization (`tsum_coe_mul_geometric_from_negBinom`);
* the descending-factorial reformulation `∑' n, (n+k) descFactorial k · rⁿ =
  k!/(1 − r)^(k+1)`, the exact "descending-factorial weighted geometric series"
  the open question names;
* a concrete evaluation `∑' n, binom(n+2, 2)·(1/2)ⁿ = 8`.

Every statement is a thin, named wrapper around Mathlib's negative-binomial
machinery; the parent-recovering identity and the descending-factorial identity
are genuine derivations combining several of these wrappers.

Status: 0 axioms, 0 sorries
-/

namespace GeometricSeriesOQ06OQ02

open scoped Topology

-- ============================================================================
-- Part I: The negative-binomial series over a normed field
-- ============================================================================

variable {𝕜 : Type*} [NormedField 𝕜]

/-- **Negative-binomial series, `HasSum` form.** For every `k` and `‖r‖ < 1` the
partial sums of `binom(n+k, k)·rⁿ` converge to `1/(1 − r)^(k+1)`.  This is the
`k`-fold term-by-term derivative (÷ `k!`) of the geometric series. -/
theorem hasSum_choose_mul_geometric (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => ((n + k).choose k : 𝕜) * r ^ n) (1 / (1 - r) ^ (k + 1)) :=
  hasSum_choose_mul_geometric_of_norm_lt_one k hr

/-- The negative-binomial series is summable when `‖r‖ < 1`. -/
theorem summable_choose_mul_geometric (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n + k).choose k : 𝕜) * r ^ n) :=
  (hasSum_choose_mul_geometric k hr).summable

/-- **Negative-binomial series.** For every `k` and `‖r‖ < 1`,

    ∑' n, binom(n+k, k) · rⁿ = 1 / (1 − r)^(k+1). -/
theorem tsum_choose_mul_geometric (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, ((n + k).choose k : 𝕜) * r ^ n = 1 / (1 - r) ^ (k + 1) :=
  (hasSum_choose_mul_geometric k hr).tsum_eq

-- ============================================================================
-- Part II: The anchoring specializations k = 0 and k = 1
-- ============================================================================

/-- **`k = 0` recovers the geometric series.** Since `binom(n, 0) = 1`, the family
degenerates to `∑' n, rⁿ = 1/(1 − r)`, the seed of the whole differentiation
tower. -/
theorem tsum_geometric_of_negBinom {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, r ^ n = 1 / (1 - r) := by
  have h := tsum_choose_mul_geometric 0 hr
  simpa using h

/-- **`k = 1` gives the shifted companion.** Since `binom(n+1, 1) = n + 1`,

    ∑' n, (n + 1) · rⁿ = 1 / (1 − r)². -/
theorem tsum_succ_mul_geometric {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, ((n : 𝕜) + 1) * r ^ n = 1 / (1 - r) ^ 2 := by
  have h := tsum_choose_mul_geometric 1 hr
  have hcongr : (fun n : ℕ => ((n + 1).choose 1 : 𝕜) * r ^ n)
      = fun n : ℕ => ((n : 𝕜) + 1) * r ^ n := by
    funext n
    simp [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  rw [hcongr] at h
  exact h

-- ============================================================================
-- Part III: Closing the loop — recover the parent's arithmetico-geometric sum
-- ============================================================================

/-- **The parent result is the `k = 1` case minus the `k = 0` case.** Subtracting
the geometric series from the shifted companion strips the `+1`, recovering the
parent entry's arithmetico-geometric first moment

    ∑' n, n · rⁿ = r / (1 − r)²

purely from the negative-binomial family.  This is the precise sense in which the
`k`-fold differentiation "generalizes cleanly": the parent is a special case. -/
theorem tsum_coe_mul_geometric_from_negBinom {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : 𝕜) * r ^ n = r / (1 - r) ^ 2 := by
  have hne : (1 : 𝕜) - r ≠ 0 := by
    rcases eq_or_ne r 1 with rfl | hr1
    · simp at hr
    · exact sub_ne_zero.mpr (Ne.symm hr1)
  -- `∑ (n+1)·rⁿ = 1/(1−r)²` and `∑ rⁿ = 1/(1−r)`, both as `HasSum`.
  have h1 : HasSum (fun n : ℕ => ((n : 𝕜) + 1) * r ^ n) (1 / (1 - r) ^ 2) := by
    have h := hasSum_choose_mul_geometric 1 hr
    have hcongr : (fun n : ℕ => ((n + 1).choose 1 : 𝕜) * r ^ n)
        = fun n : ℕ => ((n : 𝕜) + 1) * r ^ n := by
      funext n
      simp [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    rwa [hcongr] at h
  have h0 : HasSum (fun n : ℕ => r ^ n) (1 / (1 - r)) := by
    have h := hasSum_choose_mul_geometric 0 hr
    simpa using h
  -- Subtract term by term: `(n+1)·rⁿ − rⁿ = n·rⁿ`.
  have hsub := h1.sub h0
  have hcongr : (fun n : ℕ => ((n : 𝕜) + 1) * r ^ n - r ^ n)
      = fun n : ℕ => (n : 𝕜) * r ^ n := by
    funext n; ring
  rw [hcongr] at hsub
  have hval : (1 : 𝕜) / (1 - r) ^ 2 - 1 / (1 - r) = r / (1 - r) ^ 2 := by
    field_simp
    ring
  rw [hval] at hsub
  exact hsub.tsum_eq

-- ============================================================================
-- Part IV: The descending-factorial reformulation
-- ============================================================================

/-- **Descending-factorial weighted geometric series.** Because
`(n+k) descFactorial k = k! · binom(n+k, k)`, the negative-binomial series
rescales to

    ∑' n, (n+k) descFactorial k · rⁿ = k! / (1 − r)^(k+1),

the "descending-factorial weighted geometric series" named in the open question.
For `k = 1` this is again `∑' n, (n+1)·rⁿ = 1/(1 − r)²`. -/
theorem tsum_descFactorial_mul_geometric (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, ((n + k).descFactorial k : 𝕜) * r ^ n
      = (k.factorial : 𝕜) / (1 - r) ^ (k + 1) := by
  have h := (hasSum_choose_mul_geometric k hr).mul_left (k.factorial : 𝕜)
  have hcongr : (fun n : ℕ => (k.factorial : 𝕜) * (((n + k).choose k : 𝕜) * r ^ n))
      = fun n : ℕ => ((n + k).descFactorial k : 𝕜) * r ^ n := by
    funext n
    rw [Nat.descFactorial_eq_factorial_mul_choose (n + k) k]
    push_cast
    ring
  rw [hcongr] at h
  rw [h.tsum_eq]
  rw [one_div, mul_one_div]

-- ============================================================================
-- Part V: A concrete evaluation
-- ============================================================================

/-- **Concrete value.** Taking `k = 2`, `r = 1/2` over `ℝ`:

    ∑' n, binom(n+2, 2) · (1/2)ⁿ = 8,

since `1/(1 − 1/2)³ = 2³ = 8`.  The triangular-number weights `binom(n+2, 2) =
(n+1)(n+2)/2` are exactly the coefficients of the second derivative of the
geometric series. -/
theorem tsum_choose_two_half_pow :
    ∑' n : ℕ, ((n + 2).choose 2 : ℝ) * (1 / 2) ^ n = 8 := by
  have h : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
  rw [tsum_choose_mul_geometric 2 h]
  norm_num

-- ============================================================================
-- Part VI: Summary
-- ============================================================================

/-
## Summary

| Result | Statement | Backing |
|--------|-----------|---------|
| `hasSum_choose_mul_geometric` | partial sums → 1/(1−r)^(k+1) | `hasSum_choose_mul_geometric_of_norm_lt_one` |
| `tsum_choose_mul_geometric` | ∑ binom(n+k,k)·rⁿ = 1/(1−r)^(k+1) | `HasSum.tsum_eq` |
| `summable_choose_mul_geometric` | negative-binomial series summable | `HasSum.summable` |
| `tsum_geometric_of_negBinom` | `k=0` → ∑ rⁿ = 1/(1−r) | specialize k = 0 |
| `tsum_succ_mul_geometric` | `k=1` → ∑ (n+1)·rⁿ = 1/(1−r)² | specialize k = 1 |
| `tsum_coe_mul_geometric_from_negBinom` | ∑ n·rⁿ = r/(1−r)² (parent) | `k=1` − `k=0` |
| `tsum_descFactorial_mul_geometric` | ∑ (n+k)‿ₖ·rⁿ = k!/(1−r)^(k+1) | rescale by `k!` |
| `tsum_choose_two_half_pow` | ∑ binom(n+2,2)·(1/2)ⁿ = 8 | specialize k = 2, r = 1/2 |

**Answer to the open question.** The term-by-term differentiation generalizes
cleanly: the `k`-fold derivative of `∑ rⁿ = 1/(1 − r)`, normalized by `k!`, is the
negative-binomial series `∑ binom(n+k, k)·rⁿ = 1/(1 − r)^(k+1)`, and the parent's
arithmetico-geometric first moment `∑ n·rⁿ = r/(1 − r)²` reappears as the `k = 1`
member of the family (minus the `k = 0` geometric series).  The descending-
factorial form `∑ (n+k) descFactorial k · rⁿ = k!/(1 − r)^(k+1)` is the same
statement with the binomial coefficient rescaled by `k!`.
-/

end GeometricSeriesOQ06OQ02

#check @GeometricSeriesOQ06OQ02.tsum_choose_mul_geometric
#check @GeometricSeriesOQ06OQ02.tsum_coe_mul_geometric_from_negBinom
#check @GeometricSeriesOQ06OQ02.tsum_descFactorial_mul_geometric
#check @GeometricSeriesOQ06OQ02.tsum_choose_two_half_pow
