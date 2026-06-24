import Mathlib

/-
# Antitone Integral Test OQ-01 → OQ-02: convergence to the Euler–Mascheroni constant

The parent file (`AntitoneIntegralSumComparison`, "The Integral Test") ran the antitone
integral comparison on `f x = 1/x` and pinned the **harmonic defect**

  `aₙ := Hₙ − log(n+1)`,   `Hₙ = harmonic n = ∑_{k=1}^{n} 1/k`

between two integrals, proving `0 ≤ aₙ` (`harmonic_sub_log_nonneg`) and
`aₙ ≤ 1` (`harmonic_succ_sub_log_le_one`).  That established **boundedness** of the defect
sequence, but stopped short of the headline consequence.

The defect is also monotone increasing, so a bounded-monotone argument forces it to
**converge**.  Its limit is the **Euler–Mascheroni constant** `γ ≈ 0.5772…`.  This file
answers the parent's open question — *does the defect converge, and to what?* — by bridging
the parent's setup to Mathlib's `Real.eulerMascheroniConstant`.

## Main results

* `tendsto_harmonic_sub_log_add_one` : the parent's exact sequence `Hₙ − log(n+1) → γ`.
* `tendsto_harmonic_sub_log` : the textbook form `Hₙ − log n → γ` — i.e. `Hₙ ∼ log n + γ`.
* `harmonic_sub_log_add_one_lt_gamma` / `gamma_lt_harmonic_sub_log` : the two parent-style
  sequences **bracket** `γ` from below and above for every `n ≥ 1`.
* `gamma_mem_Ioo` : the resulting nested enclosure `γ ∈ (Hₙ − log(n+1), Hₙ − log n)`.
* `tendsto_bracket_width` : the bracket width `log(n+1) − log n → 0`, so the enclosure pins
  `γ` to arbitrary precision.
* `gamma_pos`, `gamma_lt_one`, `gamma_mem_Ioo_half_twoThirds` : `0 < γ < 1`, sharpened to
  `1/2 < γ < 2/3`.
* `harmonic_six`, `gamma_enclosure_six` : a concrete rational bracket
  `49/20 − log 7 < γ < 49/20 − log 6`.

All statements reduce to Mathlib's Euler–Mascheroni development; the file is `sorry`-free
and `axiom`-free (standard foundations only).
-/

namespace AntitoneIntegralSumComparisonOQ01OQ02

open Filter Topology Real

/-- **Convergence of the parent's defect sequence.**  The harmonic defect
`Hₙ − log(n+1)` — the very sequence the parent file bounded in `[0,1]` — converges to the
Euler–Mascheroni constant `γ`.  This is the answer to the parent's open question. -/
theorem tendsto_harmonic_sub_log_add_one :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ) - Real.log (n + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log_add_one

/-- **Textbook form: `Hₙ − log n → γ`,** equivalently `Hₙ ∼ log n + γ`.  Shifting the
logarithm's argument from `n+1` to `n` does not change the limit, since
`log(n+1) − log n → 0`. -/
theorem tendsto_harmonic_sub_log :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ) - Real.log n) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log

/-- **Lower bracket.**  Every term of the parent's increasing sequence lies strictly below
`γ`: `Hₙ − log(n+1) < γ`. -/
theorem harmonic_sub_log_add_one_lt_gamma (n : ℕ) :
    (harmonic n : ℝ) - Real.log (n + 1) < Real.eulerMascheroniConstant := by
  have := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  simpa [Real.eulerMascheroniSeq] using this

/-- **Upper bracket.**  The companion decreasing sequence lies strictly above `γ`:
`γ < Hₙ − log n` for `n ≥ 1`. -/
theorem gamma_lt_harmonic_sub_log (n : ℕ) (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant < (harmonic n : ℝ) - Real.log n := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have hn0 : n ≠ 0 := by omega
  simpa [Real.eulerMascheroniSeq', hn0] using h

/-- **Nested enclosure.**  For every `n ≥ 1`,
`γ ∈ (Hₙ − log(n+1), Hₙ − log n)`. -/
theorem gamma_mem_Ioo (n : ℕ) (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant ∈
      Set.Ioo ((harmonic n : ℝ) - Real.log (n + 1)) ((harmonic n : ℝ) - Real.log n) :=
  ⟨harmonic_sub_log_add_one_lt_gamma n, gamma_lt_harmonic_sub_log n hn⟩

/-- **Bracket width.**  The gap between the upper and lower brackets at index `n` is
`log(n+1) − log n`. -/
theorem bracket_width (n : ℕ) :
    ((harmonic n : ℝ) - Real.log n) - ((harmonic n : ℝ) - Real.log (n + 1))
      = Real.log (n + 1) - Real.log n := by
  ring

/-- **The enclosure pins down `γ`.**  The bracket width `log(n+1) − log n` tends to `0`, so
the nested intervals from `gamma_mem_Ioo` shrink to the single point `γ`. -/
theorem tendsto_bracket_width :
    Tendsto (fun n : ℕ ↦ Real.log (n + 1) - Real.log n) atTop (𝓝 0) := by
  have h := tendsto_harmonic_sub_log.sub tendsto_harmonic_sub_log_add_one
  have hzero : Real.eulerMascheroniConstant - Real.eulerMascheroniConstant = 0 := sub_self _
  rw [hzero] at h
  refine h.congr (fun n ↦ ?_)
  ring

/-- `γ` is positive. -/
theorem gamma_pos : 0 < Real.eulerMascheroniConstant :=
  lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant

/-- `γ < 1`. -/
theorem gamma_lt_one : Real.eulerMascheroniConstant < 1 :=
  lt_trans Real.eulerMascheroniConstant_lt_two_thirds (by norm_num)

/-- **Sharp numeric bounds:** `1/2 < γ < 2/3`. -/
theorem gamma_mem_Ioo_half_twoThirds :
    Real.eulerMascheroniConstant ∈ Set.Ioo (1 / 2 : ℝ) (2 / 3) :=
  ⟨Real.one_half_lt_eulerMascheroniConstant, Real.eulerMascheroniConstant_lt_two_thirds⟩

/-- The sixth harmonic number `H₆ = 1 + 1/2 + ⋯ + 1/6 = 49/20`. -/
theorem harmonic_six : (harmonic 6 : ℝ) = 49 / 20 := by
  norm_num [harmonic, Finset.sum_range_succ]

/-- **Concrete rational enclosure at `n = 6`:** `49/20 − log 7 < γ < 49/20 − log 6`. -/
theorem gamma_enclosure_six :
    (49 / 20 : ℝ) - Real.log 7 < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (49 / 20 : ℝ) - Real.log 6 := by
  have hlo := harmonic_sub_log_add_one_lt_gamma 6
  have hhi := gamma_lt_harmonic_sub_log 6 (by norm_num)
  rw [harmonic_six] at hlo hhi
  norm_num at hlo hhi
  exact ⟨by linarith [hlo], by linarith [hhi]⟩

end AntitoneIntegralSumComparisonOQ01OQ02
