import Mathlib
import Proofs.FatouLemma

/-
# Fatou OQ-01-OQ-02: why dominated convergence cannot close Fatou's strict gap

**Open Question (parent `FatouLemma`, openQuestions[1]).** The parent entry
proves Fatou's lemma `∫⁻ liminfₙ fₙ ≤ liminfₙ ∫⁻ fₙ` and exhibits the
escaping-mass sequence `escaping n = 𝟙_[n,n+1)` as a witness that the inequality
is *strict*: `∫⁻ liminfₙ escaping n = 0 < 1 = liminfₙ ∫⁻ escaping n`. The open
question asks to connect this to the Fatou ⇒ dominated-convergence route and to
explain, **quantitatively**, why the dominated convergence theorem (DCT) does not
rescue the escaping-mass gap.

## The Fatou ⇒ DCT route

The dominated convergence theorem is the partner of Fatou's lemma: it is exactly
Fatou's inequality bracketed on both sides. Mathlib records this as
`MeasureTheory.tendsto_lintegral_of_dominated_convergence`, whose proof *is* the
two-sided Fatou sandwich — `lintegral_liminf_le` gives `∫⁻ F ≤ liminfₙ ∫⁻ fₙ`,
the reverse Fatou `limsup_lintegral_le` gives `limsupₙ ∫⁻ fₙ ≤ ∫⁻ F`, and
`tendsto_of_le_liminf_of_limsup_le` closes the squeeze. The decisive hypothesis
of that theorem is the existence of an **integrable majorant** `g` with
`fₙ ≤ g` and `∫⁻ g < ∞`: it is what powers the reverse Fatou step.

## What is new here

This file makes precise *why that hypothesis is unavoidable* on the
escaping-mass example — formalizing the claim asserted only informally in the
parent entry. We prove:

* `escaping_no_integrable_majorant` — **every** `g` dominating all the bumps
  (`escaping n ≤ g` for all `n`) has `∫⁻ g = ∞`. The pointwise supremum of the
  bumps is the indicator of `[0, ∞)`, of infinite Lebesgue mass, so no integrable
  majorant exists.
* `escaping_not_dominated` — consequently the domination hypothesis of DCT can
  **never** be met for this sequence.
* `escaping_dct_failure` — the package: `escaping n → 0` pointwise, yet
  `∫⁻ escaping n = 1 ↛ 0 = ∫⁻ 0`, and this does **not** contradict DCT precisely
  because the sequence admits no integrable majorant. The escaping mass is the
  sharp boundary case isolating the necessity of DCT's hypothesis.

## Method

If `escaping n ≤ g` for all `n` then for `x ≥ 0` the single bump
`escaping ⌊x⌋₊` equals `1` at `x` (since `x ∈ [⌊x⌋₊, ⌊x⌋₊ + 1)`), giving
`(Set.Ici 0).indicator 1 ≤ g`; integrating yields
`∫⁻ g ≥ volume (Set.Ici 0) = ∞`.

## References

* Mathlib: `Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean`
  (`tendsto_lintegral_of_dominated_convergence`, `limsup_lintegral_le`).
* Parent `Proofs/FatouLemma.lean` (`FatouLemma.escaping`).
* Folland, *Real Analysis*, Thm 2.18 ff. (Fatou ⇒ DCT and the escaping-mass example).
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal Topology

namespace FatouLemmaOQ01OQ02

open FatouLemma

/-! ## The escaping-mass sequence admits no integrable majorant -/

/-- If `g` dominates every escaping bump, then `g` dominates the indicator of
`[0, ∞)`. Indeed, for `x ≥ 0` the single bump `escaping ⌊x⌋₊` equals `1` at `x`
(since `x ∈ [⌊x⌋₊, ⌊x⌋₊ + 1)`), and `escaping ⌊x⌋₊ ≤ g`; for `x < 0` the
indicator is `0`. This is the pointwise supremum `⨆ₙ escaping n = 𝟙_[0,∞)` in the
form needed below. -/
theorem ici_indicator_le_of_dominates {g : ℝ → ℝ≥0∞} (hdom : ∀ n, escaping n ≤ g) :
    (Set.Ici (0 : ℝ)).indicator 1 ≤ g := by
  intro x
  rcases le_or_gt 0 x with hx | hx
  · -- `x ≥ 0`: the floor bump is `1` at `x`.
    have hmem : x ∈ Set.Ico ((⌊x⌋₊ : ℝ)) ((⌊x⌋₊ : ℝ) + 1) :=
      ⟨Nat.floor_le hx, Nat.lt_floor_add_one x⟩
    have hbump : escaping ⌊x⌋₊ x = 1 := by
      unfold escaping
      rw [Set.indicator_of_mem hmem]
      rfl
    have hxi : x ∈ Set.Ici (0 : ℝ) := hx
    rw [Set.indicator_of_mem hxi]
    calc (1 : ℝ → ℝ≥0∞) x = escaping ⌊x⌋₊ x := hbump.symm
      _ ≤ g x := hdom _ x
  · -- `x < 0`: indicator is `0`.
    have hxni : x ∉ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici, not_le]; linarith
    rw [Set.indicator_of_notMem hxni]
    exact zero_le _

/-- **The escaping-mass sequence has no integrable majorant.** Every `g` with
`escaping n ≤ g` for all `n` has infinite Lebesgue integral, because it dominates
the indicator of `[0, ∞)`, whose integral is `volume (Set.Ici 0) = ∞`. This is
the precise reason the dominated convergence theorem cannot apply to the
escaping bumps. -/
theorem escaping_no_integrable_majorant {g : ℝ → ℝ≥0∞} (hdom : ∀ n, escaping n ≤ g) :
    ∫⁻ x, g x ∂(volume : Measure ℝ) = ∞ := by
  have hle := ici_indicator_le_of_dominates hdom
  have hmono : ∫⁻ x, (Set.Ici (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞) x ∂(volume : Measure ℝ)
      ≤ ∫⁻ x, g x ∂(volume : Measure ℝ) := lintegral_mono hle
  rw [lintegral_indicator_one measurableSet_Ici, Real.volume_Ici] at hmono
  exact top_le_iff.mp hmono

/-- **The domination hypothesis of DCT fails for escaping mass.** There is no
function of finite integral dominating every bump, so the dominated convergence
theorem simply does not apply to `escaping`. -/
theorem escaping_not_dominated :
    ¬ ∃ g : ℝ → ℝ≥0∞, (∫⁻ x, g x ∂(volume : Measure ℝ) ≠ ∞) ∧ (∀ n, escaping n ≤ g) := by
  rintro ⟨g, hfin, hdom⟩
  exact hfin (escaping_no_integrable_majorant hdom)

/-! ## The escaping mass: pointwise limit `0`, integrals constant `1` -/

/-- At every point `x`, the sequence `n ↦ escaping n x` converges to `0`: once
`n ≥ ⌊x⌋₊ + 1` the bump has marched strictly to the right of `x`. (The parent's
`escaping_liminf_zero` records only the `liminf`; here we expose the full limit,
needed to phrase the DCT-failure package.) -/
theorem escaping_tendsto_zero (x : ℝ) :
    Tendsto (fun n => escaping n x) atTop (𝓝 0) := by
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

/-- The escaping-mass integrals are constantly `1`, hence converge to `1` — not
to `∫⁻ (pointwise limit) = ∫⁻ 0 = 0`. -/
theorem escaping_lintegral_tendsto_one :
    Tendsto (fun n => ∫⁻ x, escaping n x ∂(volume : Measure ℝ)) atTop (𝓝 1) := by
  simp only [escaping_lintegral]
  exact tendsto_const_nhds

/-! ## The headline: a sharp instance where DCT's hypothesis is necessary -/

/-- **Escaping mass is the sharp boundary case for DCT.** The bumps converge
pointwise to `0`, yet their integrals converge to `1`, not to the integral
`0` of the limit:
```
  escaping n x → 0   (∀ x),     ∫⁻ escaping n → 1 ≠ 0 = ∫⁻ 0.
```
This is **not** a contradiction with the dominated convergence theorem, because
the escaping sequence has no integrable majorant (`escaping_not_dominated`) — DCT
never applied. The failure of `∫⁻ escaping n → ∫⁻ (lim)` together with the
failure of domination shows that DCT's integrable-majorant hypothesis cannot be
dropped. -/
theorem escaping_dct_failure :
    (∀ x, Tendsto (fun n => escaping n x) atTop (𝓝 0)) ∧
    (Tendsto (fun n => ∫⁻ x, escaping n x ∂(volume : Measure ℝ)) atTop (𝓝 1)) ∧
    (∫⁻ _x, (0 : ℝ≥0∞) ∂(volume : Measure ℝ) = 0) ∧
    ¬ ∃ g : ℝ → ℝ≥0∞, (∫⁻ x, g x ∂(volume : Measure ℝ) ≠ ∞) ∧ (∀ n, escaping n ≤ g) :=
  ⟨escaping_tendsto_zero, escaping_lintegral_tendsto_one, lintegral_zero, escaping_not_dominated⟩

end FatouLemmaOQ01OQ02
