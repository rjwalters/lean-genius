/-
# Erdős Problem #1013 (oq-01): the asymptotic constant links the two open questions

Erdős #1013 asks for the asymptotics of `h₃(k)` — the least number of vertices in a
triangle-free graph of chromatic number `k` — and, separately, whether
`h₃(k+1)/h₃(k) → 1`.  The known bounds are

    (log k / log log k)·k²  ≪  h₃(k)  ≪  (log k)·k²,

and it is conjectured that `h₃(k) ~ c·k²·log k` for a constant `c` (necessarily in
`[1/2, 1]`).  The *exact* constant `c` is OPEN.

This file does **not** determine `c`.  Instead it proves a structural fact about the
constant that holds for *every* value of `c`:

  * `constant_unique`     — the asymptotic constant, if it exists, is unique;
  * `scale_ratio_tendsto_one` — the analytic core: `((k+1)²·log(k+1)) / (k²·log k) → 1`;
  * `ratio_tendsto_one`   — if `h(k)/(k²·log k) → c` with `c > 0`, then
                            `h(k+1)/h(k) → 1`;
  * `asymptotic_subsumes_ratio` — the same statement phrased for the threshold `h₃`.

Consequently the two open parts of #1013 are not independent: the existence of the
asymptotic constant *implies* ratio convergence.  The results are stated for an
arbitrary candidate function `h : ℕ → ℝ`, so they apply verbatim to the genuine
`h₃` once (and if) its asymptotic is established.

Self-contained; no axioms beyond Lean/Mathlib foundations.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter Topology

namespace Erdos1013Constant

/-- The conjectured growth scale `g(k) = k²·log k`. -/
noncomputable def scale (k : ℕ) : ℝ := (k : ℝ) ^ 2 * Real.log k

/-- `h` has asymptotic constant `c`, i.e. `h(k) / (k²·log k) → c`. -/
def HasAsymptoticConstant (h : ℕ → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun k => h k / scale k) atTop (𝓝 c)

/-- The asymptotic constant of `h`, if it exists, is unique.  Two witnesses to the
same asymptotic must coincide, because limits in `ℝ` are unique. -/
theorem constant_unique {h : ℕ → ℝ} {c d : ℝ}
    (hc : HasAsymptoticConstant h c) (hd : HasAsymptoticConstant h d) : c = d :=
  tendsto_nhds_unique hc hd

/- ## Analytic core: the scale ratio tends to 1 -/

/-- `((k+1)² · log(k+1)) / (k² · log k) → 1`.  This is the analytic heart of the
file: the scale `k²·log k` grows so smoothly that consecutive values have ratio
tending to `1`. -/
theorem scale_ratio_tendsto_one :
    Tendsto (fun k : ℕ => scale (k + 1) / scale k) atTop (𝓝 1) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv0 : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  -- the squared linear factor `((k+1)/k)² → 1`
  have hquot : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun k : ℕ => 1 + (k : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv0
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    field_simp
  have hsq : Tendsto (fun k : ℕ => (((k : ℝ) + 1) / (k : ℝ)) ^ 2) atTop (𝓝 1) := by
    simpa using hquot.pow 2
  -- the logarithmic factor `log(k+1)/log k → 1`
  have hnum : Tendsto (fun k : ℕ => Real.log (1 + (k : ℝ)⁻¹)) atTop (𝓝 0) := by
    have hc1 : Tendsto (fun k : ℕ => 1 + (k : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hinv0
    have := ((Real.continuousAt_log (one_ne_zero)).tendsto).comp hc1
    simpa [Real.log_one] using this
  have hquotlog : Tendsto (fun k : ℕ => Real.log (1 + (k : ℝ)⁻¹) / Real.log k)
      atTop (𝓝 0) := hnum.div_atTop hlog
  have hlogratio : Tendsto (fun k : ℕ => Real.log (k + 1) / Real.log k) atTop (𝓝 1) := by
    have h1 : Tendsto (fun k : ℕ => 1 + Real.log (1 + (k : ℝ)⁻¹) / Real.log k)
        atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hquotlog
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with k hk
    have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
    have hk1ne : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hlogne : Real.log (k : ℝ) ≠ 0 := (Real.log_pos hk1).ne'
    have hsplit : Real.log (1 + (k : ℝ)⁻¹) = Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
      rw [show (1 + (k : ℝ)⁻¹) = ((k : ℝ) + 1) / (k : ℝ) by field_simp,
        Real.log_div hk1ne hkne]
    rw [hsplit]
    field_simp
    ring
  -- assemble the two factors
  have hmul : Tendsto
      (fun k : ℕ => (((k : ℝ) + 1) / (k : ℝ)) ^ 2 * (Real.log (k + 1) / Real.log k))
      atTop (𝓝 (1 * 1)) := hsq.mul hlogratio
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with k hk
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hlogne : Real.log (k : ℝ) ≠ 0 := (Real.log_pos hk1).ne'
  simp only [scale]
  push_cast
  field_simp

/- ## Main reduction -/

/-- **If the asymptotic constant exists, ratio convergence is automatic.**
Given `h(k)/(k²·log k) → c` with `c > 0`, we have `h(k+1)/h(k) → 1`.  The proof
factors `h(k+1)/h(k)` as `(h(k+1)/scale(k+1)) · (scale(k+1)/scale(k)) / (h(k)/scale(k))`,
whose three factors tend to `c`, `1`, and `c` respectively, giving `c·1/c = 1`. -/
theorem ratio_tendsto_one {h : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hasym : HasAsymptoticConstant h c) :
    Tendsto (fun k => h (k + 1) / h k) atTop (𝓝 1) := by
  have hshift : Tendsto (fun k : ℕ => h (k + 1) / scale (k + 1)) atTop (𝓝 c) := by
    simpa [Function.comp] using hasym.comp (tendsto_add_atTop_nat 1)
  have hnum : Tendsto
      (fun k : ℕ => (h (k + 1) / scale (k + 1)) * (scale (k + 1) / scale k))
      atTop (𝓝 (c * 1)) := hshift.mul scale_ratio_tendsto_one
  rw [mul_one] at hnum
  have hfrac : Tendsto
      (fun k : ℕ =>
        ((h (k + 1) / scale (k + 1)) * (scale (k + 1) / scale k)) / (h k / scale k))
      atTop (𝓝 (c / c)) := hnum.div hasym hc.ne'
  rw [div_self hc.ne'] at hfrac
  refine hfrac.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with k hk
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hlogne : Real.log (k : ℝ) ≠ 0 := (Real.log_pos hk1).ne'
  have hk1' : (1 : ℝ) < ((k : ℝ) + 1) := by linarith
  have hsk : scale k ≠ 0 := by
    simp only [scale]; exact mul_ne_zero (pow_ne_zero 2 hkne) hlogne
  have hsk1 : scale (k + 1) ≠ 0 := by
    simp only [scale]; push_cast
    exact mul_ne_zero (pow_ne_zero 2 (by positivity : (0 : ℝ) < (k : ℝ) + 1).ne')
      (Real.log_pos hk1').ne'
  rcases eq_or_ne (h k) 0 with hhk | hhk
  · simp [hhk]
  · field_simp

/- ## Statement for the genuine threshold function -/

/-- **Erdős #1013, structural reduction.**  For the genuine triangle-free chromatic
threshold `h₃` (here any candidate `h₃ : ℕ → ℝ`), if the asymptotic
`h₃(k) ~ c·k²·log k` holds for some `c > 0`, then the separately-posed open question
`h₃(k+1)/h₃(k) → 1` holds automatically.  Hence the asymptotic-constant question of
#1013 subsumes its ratio-convergence question. -/
theorem asymptotic_subsumes_ratio (h₃ : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hasym : Tendsto (fun k => h₃ k / ((k : ℝ) ^ 2 * Real.log k)) atTop (𝓝 c)) :
    Tendsto (fun k => h₃ (k + 1) / h₃ k) atTop (𝓝 1) :=
  ratio_tendsto_one hc hasym

end Erdos1013Constant
