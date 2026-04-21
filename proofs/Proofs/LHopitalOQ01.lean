/-
# L'Hôpital's Rule: Counterexample to the Converse (OQ-01)

## What This Proves

A counterexample showing that the CONVERSE of L'Hôpital's rule fails:

  f(x) = x + sin(x),  g(x) = x

**Forward direction (holds):** lim_{x→∞} f(x)/g(x) = 1
**Converse fails:** The limit lim_{x→∞} f'(x)/g'(x) = lim_{x→∞} (1 + cos x)/1 does NOT EXIST.

This demonstrates that L'Hôpital's rule is one-directional:
  "lim f'/g' exists ⟹ lim f/g = lim f'/g'"
but NOT:
  "lim f/g exists ⟹ lim f'/g' exists"

## Proof Strategy

**Part 1 — lim (x + sin x)/x = 1:**
- Write (x + sin x)/x = 1 + (sin x)/x
- Since |sin x| ≤ 1, we have |sin x / x| ≤ 1/x for x > 0
- Direct ε-N: for x > 1/ε + 1, we get 1/x < ε
- Therefore (x + sin x)/x → 1

**Part 2 — lim (1 + cos x) diverges:**
- cos(n * 2π) = 1, so 1 + cos(n * 2π) = 2 for all n ∈ ℕ
- cos(n * 2π + π) = -1, so 1 + cos(n * 2π + π) = 0 for all n ∈ ℕ
- Both sequences n * 2π and n * 2π + π tend to ∞
- If L = lim (1 + cos x) existed, it would equal both 2 and 0 — impossible.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Separation.Hausdorff

namespace LHopitalConverse

open Real Filter Topology

-- ============================================================
-- PART I: lim (x + sin x) / x = 1
-- ============================================================

/-- Key helper: sin(x) / x → 0 as x → ∞.
    Direct ε-N proof: for x > 1/ε + 1, we have |sin x / x| ≤ 1/x < ε. -/
lemma tendsto_sin_div_atTop :
    Tendsto (fun x : ℝ => Real.sin x / x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨1/ε + 1, fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < x :=
    lt_of_lt_of_le (add_pos (div_pos one_pos hε) one_pos) hx
  rw [Real.dist_eq, sub_zero]
  have habs : |Real.sin x / x| = |Real.sin x| / x := by
    rw [abs_div, abs_of_pos hxpos]
  rw [habs]
  have hbound : |Real.sin x| / x ≤ 1 / x := by
    gcongr
    exact Real.abs_sin_le_one x
  have hsmall : 1 / x < ε := by
    have hxε : 1/ε < x := by linarith
    have hprod : ε * (1/ε) < ε * x := mul_lt_mul_of_pos_left hxε hε
    rw [mul_one_div_cancel hε.ne'] at hprod  -- hprod : 1 < ε * x
    have hkey : 0 < (ε * x - 1) / x := div_pos (by linarith) hxpos
    have expand : (ε * x - 1) / x = ε - 1 / x := by field_simp
    linarith [expand ▸ hkey]
  linarith

/-- The main limit: (x + sin x) / x → 1 as x → ∞. -/
theorem lim_ratio_eq_one :
    Tendsto (fun x : ℝ => (x + Real.sin x) / x) atTop (𝓝 1) := by
  have hrewrite : ∀ᶠ x : ℝ in atTop, (x + Real.sin x) / x = 1 + Real.sin x / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  rw [tendsto_congr' hrewrite]
  have hsin := tendsto_sin_div_atTop
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using hone.add hsin

-- ============================================================
-- PART II: Derivative ratio (1 + cos x) has no limit
-- ============================================================

/-- The sequence n * 2π tends to +∞ as n : ℕ → ∞. -/
private lemma seq1_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) * (2 * Real.pi)) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_const' (by positivity)

/-- The sequence n * 2π + π tends to +∞ as n : ℕ → ∞. -/
private lemma seq2_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) * (2 * Real.pi) + Real.pi) atTop atTop :=
  tendsto_atTop_mono (fun n => le_add_of_nonneg_right Real.pi_pos.le) seq1_atTop

/-- At multiples of 2π, the function 1 + cos equals 2. -/
private lemma val_on_seq1 (n : ℕ) : 1 + Real.cos ((n : ℝ) * (2 * Real.pi)) = 2 := by
  rw [Real.cos_nat_mul_two_pi]; ring

/-- At odd multiples of π, the function 1 + cos equals 0. -/
private lemma val_on_seq2 (n : ℕ) : 1 + Real.cos ((n : ℝ) * (2 * Real.pi) + Real.pi) = 0 := by
  rw [Real.cos_nat_mul_two_pi_add_pi]; ring

/-- The function 1 + cos x has no limit as x → ∞:
    it equals 2 along n*2π (→ ∞) and 0 along n*2π+π (→ ∞). -/
theorem deriv_ratio_no_limit :
    ¬∃ L : ℝ, Tendsto (fun x : ℝ => 1 + Real.cos x) atTop (𝓝 L) := by
  intro ⟨L, hL⟩
  -- Subsequential limit along n * 2π
  have hcomp1 : Tendsto (fun n : ℕ => 1 + Real.cos ((n : ℝ) * (2 * Real.pi))) atTop (𝓝 L) :=
    hL.comp seq1_atTop
  -- Along this subsequence, the function constantly equals 2
  have hseq1_limit : Tendsto (fun n : ℕ => 1 + Real.cos ((n : ℝ) * (2 * Real.pi))) atTop (𝓝 2) :=
    (tendsto_congr (fun n => (val_on_seq1 n).symm)).mp tendsto_const_nhds
  -- By uniqueness of limits: L = 2
  have hL2 : L = 2 := tendsto_nhds_unique hcomp1 hseq1_limit
  -- Subsequential limit along n * 2π + π
  have hcomp2 : Tendsto (fun n : ℕ => 1 + Real.cos ((n : ℝ) * (2 * Real.pi) + Real.pi)) atTop (𝓝 L) :=
    hL.comp seq2_atTop
  -- Along this subsequence, the function constantly equals 0
  have hseq2_limit : Tendsto (fun n : ℕ => 1 + Real.cos ((n : ℝ) * (2 * Real.pi) + Real.pi)) atTop (𝓝 0) :=
    (tendsto_congr (fun n => (val_on_seq2 n).symm)).mp tendsto_const_nhds
  -- By uniqueness of limits: L = 0
  have hL0 : L = 0 := tendsto_nhds_unique hcomp2 hseq2_limit
  -- L = 2 and L = 0 is a contradiction
  linarith [hL2.symm.trans hL0]

-- ============================================================
-- PART III: Main theorem
-- ============================================================

/-- **Main Theorem (Converse L'Hôpital Counterexample)**:
    f(x) = x + sin x, g(x) = x satisfy lim f/g = 1, but lim f'/g' does not exist.
    This shows that the existence of lim f/g does NOT imply existence of lim f'/g'. -/
theorem lhopital_converse_fails :
    (Tendsto (fun x : ℝ => (x + Real.sin x) / x) atTop (𝓝 1)) ∧
    (¬∃ L : ℝ, Tendsto (fun x : ℝ => (1 + Real.cos x) / 1) atTop (𝓝 L)) := by
  refine ⟨lim_ratio_eq_one, fun ⟨L, hL⟩ => deriv_ratio_no_limit ⟨L, ?_⟩⟩
  simpa using hL

end LHopitalConverse
