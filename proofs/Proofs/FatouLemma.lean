import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-
# Fatou's Lemma and the Strictness of the Liminf Inequality

## What This Proves

**Fatou's lemma** is one of the three pillars of Lebesgue integration. For a
sequence of nonnegative measurable functions `fₙ : α → ℝ≥0∞`,
```
  ∫⁻ liminfₙ fₙ ≤ liminfₙ ∫⁻ fₙ.
```
The integral of the pointwise liminf is at most the liminf of the integrals.
This inequality is `MeasureTheory.lintegral_liminf_le` in Mathlib; we restate it
cleanly in the `Measurable` and `AEMeasurable` forms as
`fatou_lintegral_liminf_le` and `fatou_lintegral_liminf_le'` — the headline
statements for the gallery.

The mathematical substance of this file is the **escaping-mass witness** proving
that Fatou's inequality is *genuinely strict*:

* `escaping n = 𝟙_[n,n+1)` is a unit bump marching off to `+∞` along the real
  line. Each bump carries unit Lebesgue mass, but at any fixed point the
  sequence is eventually `0`.

* `escaping_lintegral` — every bump has integral `1`: `∫⁻ escaping n = 1`. This
  is the conserved quantity that escapes to infinity.

* `escaping_liminf_zero` — at every point `x` the sequence `n ↦ escaping n x` is
  eventually `0` (once `n > x` we have `x ∉ [n,n+1)`), so its liminf is `0`.

* `fatou_strict_on_escaping` — the strict gap:
  `∫⁻ liminfₙ escaping n = 0 < 1 = liminfₙ ∫⁻ escaping n`.
  The unit mass of each bump survives in *every* integral but vanishes from the
  pointwise liminf.

This is exactly *why* Fatou's lemma is only an inequality, and why the monotone
and dominated convergence theorems need their extra hypotheses to recover
equality: mass can escape to infinity and be lost in the pointwise liminf.

## Why It Is Not in Mathlib

Mathlib records the inequality `lintegral_liminf_le` but no witness that it is
strict. The escaping-mass sequence, the unit-mass and eventually-zero
computations, and the strict-gap conclusion are the new content. (The same
loss-of-mass-to-infinity phenomenon is the witness requested by the Egorov
entry's follow-up question, measured there by uniform convergence rather than
by the integral.)

## Axiom Status

Fully verified, 0 sorries, 0 `axiom` declarations, no `native_decide`. Relies
only on Mathlib's measure theory and the foundational axioms `propext`,
`Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace FatouLemma

/-! ## Fatou's lemma (Mathlib restatements) -/

/-- **Fatou's lemma.** For measurable nonnegative functions `fₙ : α → ℝ≥0∞`, the
integral of the pointwise liminf is at most the liminf of the integrals. This is
`MeasureTheory.lintegral_liminf_le`, restated as the headline `Measurable` form. -/
theorem fatou_lintegral_liminf_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  lintegral_liminf_le hf

/-- **Fatou's lemma, `AEMeasurable` form.** The same inequality assuming each
`fₙ` is only almost-everywhere measurable, via
`MeasureTheory.lintegral_liminf_le'`. -/
theorem fatou_lintegral_liminf_le' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  lintegral_liminf_le' hf

/-! ## The escaping-mass sequence `𝟙_[n,n+1)` -/

/-- The marching-indicator sequence `escaping n = 𝟙_[n,n+1)`: a unit bump on the
half-open interval `[n, n+1)` of the real line, escaping to `+∞` as `n → ∞`. -/
noncomputable def escaping (n : ℕ) : ℝ → ℝ≥0∞ := (Set.Ico (n : ℝ) (n + 1)).indicator 1

/-- Each bump is measurable: it is the indicator of a measurable interval. -/
theorem escaping_measurable (n : ℕ) : Measurable (escaping n) :=
  measurable_one.indicator measurableSet_Ico

/-- Each bump carries **unit Lebesgue mass**: `∫⁻ escaping n = vol[n,n+1) = 1`.
This is the conserved quantity that escapes to infinity. -/
theorem escaping_lintegral (n : ℕ) :
    ∫⁻ x, escaping n x ∂(volume : Measure ℝ) = 1 := by
  unfold escaping
  rw [lintegral_indicator_one measurableSet_Ico, Real.volume_Ico,
    show (n : ℝ) + 1 - n = 1 by ring, ENNReal.ofReal_one]

/-- At **every** point `x` the sequence `n ↦ escaping n x` is eventually `0`:
once `n > x` we have `x ∉ [n, n+1)`, so the bump has moved past `x`. Hence the
sequence converges to `0` and its `liminf` is `0` — the pointwise computation
driving the strict gap. -/
theorem escaping_liminf_zero (x : ℝ) :
    liminf (fun n => escaping n x) atTop = 0 := by
  have h : Tendsto (fun n => escaping n x) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (⌊x⌋₊ + 1)] with n hn
    have hxn : x < (n : ℝ) := by
      have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hnot : x ∉ Set.Ico (n : ℝ) (n + 1) := by
      rw [Set.mem_Ico]; push_neg; intro h; linarith
    show (0 : ℝ≥0∞) = escaping n x
    unfold escaping
    rw [Set.indicator_of_notMem hnot]
  exact h.liminf_eq

/-! ## The headline result: Fatou's inequality is strict -/

/-- **Fatou's inequality is genuinely strict.** On the escaping-mass example,
```
  ∫⁻ liminfₙ escaping n = 0  <  1 = liminfₙ ∫⁻ escaping n.
```
The unit mass of every bump survives in each integral (right side `= 1`) but the
pointwise liminf is identically `0` (left side `= 0`), because each point is
eventually left behind by the marching interval. This is the witness — absent
from Mathlib — that Fatou's lemma cannot be upgraded to an equality without
further hypotheses. -/
theorem fatou_strict_on_escaping :
    ∫⁻ x, liminf (fun n => escaping n x) atTop ∂(volume : Measure ℝ)
      < liminf (fun n => ∫⁻ x, escaping n x ∂(volume : Measure ℝ)) atTop := by
  have hL : ∫⁻ x, liminf (fun n => escaping n x) atTop ∂(volume : Measure ℝ) = 0 := by
    simp only [escaping_liminf_zero, lintegral_zero]
  have hR : liminf (fun n => ∫⁻ x, escaping n x ∂(volume : Measure ℝ)) atTop = 1 := by
    simp only [escaping_lintegral, liminf_const]
  rw [hL, hR]
  exact zero_lt_one

end FatouLemma
