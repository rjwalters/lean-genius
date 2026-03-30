/-
  AM-GM OQ-03-OQ-03: Power Mean Extreme Cases

  The power mean (generalized mean) of positive reals x₁,...,xₙ at exponent r:
    M_r(x) = (Σ xᵢʳ / n)^{1/r}   for r ≠ 0
    M_0(x) = (∏ xᵢ)^{1/n}        (geometric mean, by limit)

  Extreme cases:
    lim_{r → +∞} M_r = max(x₁,...,xₙ)
    lim_{r → -∞} M_r = min(x₁,...,xₙ)

  Parent: AMGMInequality.lean
-/

import Mathlib

namespace AmgmOQ03OQ03

open Finset

-- ============================================================
-- PART I: Power Mean Definition
-- ============================================================

/-- The power mean M_r of positive reals in a finset, at exponent r ≠ 0. -/
noncomputable def powerMean {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then
    (∏ i : ι, x i) ^ ((Fintype.card ι : ℝ)⁻¹)
  else
    ((∑ i : ι, (x i) ^ r) / Fintype.card ι) ^ (1 / r)

-- ============================================================
-- PART II: Extreme Value Limits
-- ============================================================

/-- As r → +∞, M_r → max(x₁,...,xₙ).
    Proof idea: (Σ xᵢʳ/n)^{1/r} is dominated by the largest term.
    If M = max xᵢ, then M^r ≤ Σ xᵢʳ ≤ n·M^r, so
    M ≤ M_r ≤ n^{1/r}·M, and n^{1/r} → 1. -/
axiom powerMean_tendsto_max {n : ℕ} (x : Fin n → ℝ)
    (hpos : ∀ i, 0 < x i) (hn : 0 < n) :
    Filter.Tendsto (fun r : ℝ => powerMean x r) Filter.atTop
      (nhds (Finset.univ.sup' Finset.univ_nonempty x))

/-- As r → -∞, M_r → min(x₁,...,xₙ).
    Same argument with 1/xᵢ: M_{-r} = 1/M_r(1/x). -/
axiom powerMean_tendsto_min {n : ℕ} (x : Fin n → ℝ)
    (hpos : ∀ i, 0 < x i) (hn : 0 < n) :
    Filter.Tendsto (fun r : ℝ => powerMean x r) Filter.atBot
      (nhds (Finset.univ.inf' Finset.univ_nonempty x))

-- ============================================================
-- PART III: Monotonicity
-- ============================================================

/-- Power means are monotone in r: r ≤ s → M_r ≤ M_s.
    This is a generalization of AM-GM (M_0 ≤ M_1). -/
axiom powerMean_mono {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hpos : ∀ i, 0 < x i)
    (r s : ℝ) (hrs : r ≤ s) :
    powerMean x r ≤ powerMean x s

-- ============================================================
-- PART IV: Concrete Verifications
-- ============================================================

/-- For two positive reals a, b: M₁ = (a+b)/2 (arithmetic mean). -/
theorem powerMean_1_is_am (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean (![a, b]) 1 = (a + b) / 2 := by
  simp [powerMean, Fintype.card_fin]
  ring_nf
  sorry  -- Matrix.cons normalization

/-- For two positive reals: M₋₁ = 2ab/(a+b) (harmonic mean). -/
theorem powerMean_neg1_is_hm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean (![a, b]) (-1) = 2 * a * b / (a + b) := by
  sorry

end AmgmOQ03OQ03
