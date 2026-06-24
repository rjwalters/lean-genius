import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-
  Geometric Truncation Rate for the Arctangent Power Series (leibniz-pi-oq-01-oq-02)

  The parent entry ("Optimal Convergence Rate for Arctangent-Based Pi Series",
  leibniz-pi-oq-01) proves that the Leibniz series π/4 = Σ (-1)ⁿ/(2n+1) — the
  arctangent series evaluated at x = 1 — converges at the *boundary* rate Θ(1/N),
  and *asserts informally* that "Machin-type formulas achieve exponential
  O(1/m^(2N)) rates instead."

  This entry makes that informal claim a theorem. For the arctangent series

        arctan x = Σₙ (-1)ⁿ xⁿ⁺¹ / (2n+1)              (Real.hasSum_arctan)

  evaluated at any 0 ≤ x < 1, we prove the explicit *geometric* truncation bound

        |arctan x − Σ_{n<N} (-1)ⁿ x^(2n+1)/(2n+1)|  ≤  x^(2N+1) / (1 − x²).

  Since the right-hand side is x^(2N+1)/(1−x²) = O((x²)ᴺ), the error decays
  exponentially in N for every x strictly inside the unit interval. The Leibniz
  case x = 1 sits exactly on the boundary where the factor (1 − x²)⁻¹ blows up,
  which is precisely *why* the parent's Θ(1/N) rate is only achieved there and
  Machin-type evaluations at small x are exponentially faster.

  As a concrete corollary we bound the truncation error of Machin's formula
  4·arctan(1/5) − arctan(1/239) = π/4 after N terms of each series, exhibiting
  the (1/5)^(2N) decay.

  Engine: `Real.hasSum_arctan` (the series), `hasSum_nat_add_iff'` (the tail as a
  shifted HasSum), `hasSum_geometric_of_lt_one` (the dominating geometric series),
  and `tsum_of_norm_bounded` (direct comparison). 0 axioms, 0 sorries, no
  native_decide.
-/

namespace LeibnizPiOQ01OQ02

open Finset Real

set_option maxHeartbeats 800000

/-- The `n`-th term of the arctangent power series, matching `Real.hasSum_arctan`. -/
noncomputable def arctanTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

/-- The `N`-term truncation (partial sum) of the arctangent series at `x`. -/
noncomputable def arctanPartial (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, arctanTerm x n

/-- Each arctangent-series term is dominated in absolute value by `x^(2n+1)`
(for `x ≥ 0`): the `1/(2n+1)` factor only shrinks it. -/
theorem abs_arctanTerm_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    |arctanTerm x n| ≤ x ^ (2 * n + 1) := by
  have hpow : (0 : ℝ) ≤ x ^ (2 * n + 1) := by positivity
  have hden : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  calc |arctanTerm x n|
      = x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
        unfold arctanTerm
        rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg hpow, abs_of_nonneg (by positivity)]
    _ ≤ x ^ (2 * n + 1) := div_le_self hpow hden

/-- The arctangent series has sum `arctan x` for `0 ≤ x < 1` (specialization of
`Real.hasSum_arctan`). -/
theorem hasSum_arctanTerm {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (arctanTerm x) (arctan x) := by
  have hnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  exact Real.hasSum_arctan hnorm

/-- The dominating geometric tail: `Σᵢ x^(2(i+N)+1) = x^(2N+1) · (1−x²)⁻¹`. -/
theorem hasSum_geom_tail {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    HasSum (fun i : ℕ => x ^ (2 * (i + N) + 1))
      (x ^ (2 * N + 1) * (1 - x ^ 2)⁻¹) := by
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have hx2lt : x ^ 2 < 1 := by nlinarith
  have hgeo : HasSum (fun i : ℕ => (x ^ 2) ^ i) (1 - x ^ 2)⁻¹ :=
    hasSum_geometric_of_lt_one hx2 hx2lt
  have hgeo' : HasSum (fun i : ℕ => x ^ (2 * N + 1) * (x ^ 2) ^ i)
      (x ^ (2 * N + 1) * (1 - x ^ 2)⁻¹) := hgeo.mul_left _
  have hfun : (fun i : ℕ => x ^ (2 * (i + N) + 1))
      = (fun i : ℕ => x ^ (2 * N + 1) * (x ^ 2) ^ i) := by
    funext i
    rw [show 2 * (i + N) + 1 = (2 * N + 1) + 2 * i by ring, pow_add, pow_mul]
  rw [hfun]
  exact hgeo'

/-- **Geometric truncation rate for the arctangent series.**
For every `0 ≤ x < 1` and every `N`, the error of the `N`-term arctangent
partial sum is bounded by a single geometric quantity:

  `|arctan x − arctanPartial x N| ≤ x^(2N+1) / (1 − x²)`.

The bound is `O((x²)ᴺ)`, i.e. exponential decay in `N` whenever `x < 1`. -/
theorem arctan_series_error_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    |arctan x - arctanPartial x N| ≤ x ^ (2 * N + 1) / (1 - x ^ 2) := by
  -- The tail of the series, written as a shifted `HasSum`.
  have htail : HasSum (fun i => arctanTerm x (i + N))
      (arctan x - arctanPartial x N) :=
    (hasSum_nat_add_iff' N).mpr (hasSum_arctanTerm hx0 hx1)
  have heq : arctan x - arctanPartial x N = ∑' i, arctanTerm x (i + N) :=
    htail.tsum_eq.symm
  rw [heq, div_eq_mul_inv]
  -- Dominate the tail term-by-term by the geometric tail.
  have key : ‖∑' i, arctanTerm x (i + N)‖ ≤ x ^ (2 * N + 1) * (1 - x ^ 2)⁻¹ := by
    refine tsum_of_norm_bounded (hasSum_geom_tail hx0 hx1 N) (fun i => ?_)
    rw [Real.norm_eq_abs]
    exact abs_arctanTerm_le hx0 (i + N)
  rwa [Real.norm_eq_abs] at key

/-- Machin's identity (Mathlib), restated for the `1/5`, `1/239` arguments. -/
theorem machin_identity :
    4 * arctan (1 / 5 : ℝ) - arctan (1 / 239 : ℝ) = π / 4 := by
  simp only [one_div]
  exact four_mul_arctan_inv_5_sub_arctan_inv_239

/-- **Exponential rate of Machin's formula (the parent's informal claim, proved).**
Truncating each arctangent series in `4·arctan(1/5) − arctan(1/239) = π/4` after
`N` terms gives an error bounded by

  `4·(1/5)^(2N+1)/(1 − (1/5)²) + (1/239)^(2N+1)/(1 − (1/239)²)`,

which decays like `(1/5)^(2N)` — exponentially faster than the Leibniz series'
`Θ(1/N)` at `x = 1`. -/
theorem machin_partial_error_bound (N : ℕ) :
    |π / 4 - (4 * arctanPartial (1 / 5) N - arctanPartial (1 / 239) N)|
      ≤ 4 * ((1 / 5 : ℝ) ^ (2 * N + 1) / (1 - (1 / 5) ^ 2))
        + (1 / 239 : ℝ) ^ (2 * N + 1) / (1 - (1 / 239) ^ 2) := by
  have h5 : |arctan (1 / 5 : ℝ) - arctanPartial (1 / 5) N|
      ≤ (1 / 5 : ℝ) ^ (2 * N + 1) / (1 - (1 / 5) ^ 2) :=
    arctan_series_error_bound (by norm_num) (by norm_num) N
  have h239 : |arctan (1 / 239 : ℝ) - arctanPartial (1 / 239) N|
      ≤ (1 / 239 : ℝ) ^ (2 * N + 1) / (1 - (1 / 239) ^ 2) :=
    arctan_series_error_bound (by norm_num) (by norm_num) N
  -- Rewrite π/4 via Machin and split the error along the two series.
  have hsplit : π / 4 - (4 * arctanPartial (1 / 5) N - arctanPartial (1 / 239) N)
      = 4 * (arctan (1 / 5 : ℝ) - arctanPartial (1 / 5) N)
        - (arctan (1 / 239 : ℝ) - arctanPartial (1 / 239) N) := by
    rw [← machin_identity]; ring
  rw [hsplit]
  set a := arctan (1 / 5 : ℝ) - arctanPartial (1 / 5) N with ha
  set b := arctan (1 / 239 : ℝ) - arctanPartial (1 / 239) N with hb
  have htri : |4 * a - b| ≤ 4 * |a| + |b| := by
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]
  linarith [htri, h5, h239]

end LeibnizPiOQ01OQ02
