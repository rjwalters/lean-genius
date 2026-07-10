/-
# Shannon AWGN water-filling, oq-03-oq-01 — the equal-noise closed form

Source: parallel-Gaussian-channel water-filling (see
`ShannonChannelCodingAWGNOQ03OQ01.lean`, namespace `ShannonWaterFilling`, which
proves optimality of `Pᵢ⋆ = (μ − Nᵢ)₊`, the closed-form optimum
`∑ᵢ ½ log(max μ Nᵢ / Nᵢ)`, and existence/uniqueness of the water level `μ`).

That entry's `nextSteps` asks for the **equal-noise** specialisation: when all `n`
channels share one noise floor `Nᵢ ≡ c`, the water level and capacity have simple
closed forms. This file supplies them, all axiom-free / sorry-free:

* `waterBudget_const` — for constant noise, `g(μ) = n · (μ − c)₊`.
* `waterLevel_equalNoise` — the water level realising budget `P ≥ 0` is exactly
  `μ = c + P/n`; for `P > 0` it is the *unique* one (`waterLevel_equalNoise_unique`).
* `waterAlloc_rate_equalNoise` — the water-filling capacity collapses to the
  textbook `C = (n/2) · log(1 + P/(n·c))`.
* `parallelRate_le_equalNoise` — the operational statement: no feasible allocation
  beats `(n/2) · log(1 + P/(n·c))`; it is the constrained capacity of `n`
  identical parallel Gaussian channels.

`n = Fintype.card ι`; a `Nonempty ι` instance makes `n ≥ 1` so `P/n` is defined.

Tags: information-theory, shannon, awgn, water-filling, capacity, closed-form
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGNOQ03OQ01

set_option linter.unusedSectionVars false

namespace ShannonWaterFilling

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## Budget and water level for a constant noise floor -/

/-- **Constant-noise budget.**  When every channel has the same noise power `c`,
the budget function is `g(μ) = n · (μ − c)₊` with `n = Fintype.card ι`. -/
theorem waterBudget_const (N : ι → ℝ) {c : ℝ} (hN : ∀ i, N i = c) (μ : ℝ) :
    waterBudget N μ = (Fintype.card ι : ℝ) * max (μ - c) 0 := by
  unfold waterBudget waterAlloc
  simp only [hN]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Equal-noise water level.**  The level `μ = c + P/n` realises the budget `P`
(for `P ≥ 0`): every channel is active and receives depth `P/n`. -/
theorem waterLevel_equalNoise [Nonempty ι] (N : ι → ℝ) {c : ℝ} (hN : ∀ i, N i = c)
    {P : ℝ} (hP : 0 ≤ P) :
    waterBudget N (c + P / Fintype.card ι) = P := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hne : (Fintype.card ι : ℝ) ≠ 0 := hn.ne'
  rw [waterBudget_const N hN,
    show c + P / (Fintype.card ι : ℝ) - c = P / Fintype.card ι from by ring,
    max_eq_left (div_nonneg hP hn.le), mul_comm, div_mul_cancel₀ P hne]

/-- **Uniqueness of the equal-noise water level.**  For a positive budget the water
level `c + P/n` is the only solution of `g(μ) = P`. -/
theorem waterLevel_equalNoise_unique [Nonempty ι] (N : ι → ℝ) {c : ℝ}
    (hN : ∀ i, N i = c) {P : ℝ} (hP : 0 < P)
    {μ : ℝ} (hμ : waterBudget N μ = P) :
    μ = c + P / Fintype.card ι := by
  refine waterLevel_unique N hP hμ ?_
  exact waterLevel_equalNoise N hN hP.le

/-! ## The equal-noise capacity `C = (n/2)·log(1 + P/(n·c))` -/

/-- **Equal-noise capacity, closed form.**  Filling `n` identical channels of
noise `c` with total power `P ≥ 0` gives rate
`C = (n/2) · log(1 + P/(n·c))` — the classical formula for `n` parallel Gaussian
channels sharing one noise floor. -/
theorem waterAlloc_rate_equalNoise [Nonempty ι] (N : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (hN : ∀ i, N i = c) {P : ℝ} (hP : 0 ≤ P) :
    parallelRate N (waterAlloc (c + P / Fintype.card ι) N)
      = (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c)) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcne : c ≠ 0 := hc.ne'
  have hnne : (Fintype.card ι : ℝ) ≠ 0 := hn.ne'
  set μ := c + P / Fintype.card ι with hμdef
  have hμc : c ≤ μ := by
    rw [hμdef]; have : 0 ≤ P / Fintype.card ι := div_nonneg hP hn.le; linarith
  have hNpos : ∀ i, 0 < N i := fun i => by rw [hN i]; exact hc
  rw [waterAlloc_rate_closedForm N hNpos μ]
  have heq : μ / c = 1 + P / (Fintype.card ι * c) := by
    rw [hμdef]; field_simp; ring
  have hterm : ∀ i, (1 / 2) * Real.log (max μ (N i) / N i)
      = (1 / 2) * Real.log (1 + P / (Fintype.card ι * c)) := by
    intro i
    rw [hN i, max_eq_left hμc, heq]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- **Operational equal-noise capacity.**  No feasible power allocation over `n`
identical channels of noise `c` (total power `≤ P`, `P > 0`) can exceed
`(n/2) · log(1 + P/(n·c))`.  Combines optimality (`waterfilling_optimal`) with the
equal-noise water level and closed form. -/
theorem parallelRate_le_equalNoise [Nonempty ι] (N : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (hN : ∀ i, N i = c) {P : ℝ} (hP : 0 < P)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hxsum : ∑ i, x i ≤ P) :
    parallelRate N x
      ≤ (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c)) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hNpos : ∀ i, 0 < N i := fun i => by rw [hN i]; exact hc
  have hμpos : 0 < c + P / Fintype.card ι := by
    have : 0 ≤ P / Fintype.card ι := div_nonneg hP.le hn.le; linarith
  have hbudget : waterBudget N (c + P / Fintype.card ι) = P :=
    waterLevel_equalNoise N hN hP.le
  calc parallelRate N x
      ≤ parallelRate N (waterAlloc (c + P / Fintype.card ι) N) :=
        waterfilling_optimal N hNpos hμpos hbudget x hx hxsum
    _ = (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c)) :=
        waterAlloc_rate_equalNoise N hc hN hP.le

end ShannonWaterFilling
