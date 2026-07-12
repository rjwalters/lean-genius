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
    rw [hμdef, add_div, div_self hcne, div_div]
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

/-! ## Nonnegativity and power-monotonicity of the equal-noise capacity -/

/-- **The equal-noise capacity is nonnegative.**  `(n/2)·log(1 + P/(n·c)) ≥ 0` for
    `P ≥ 0`, `c > 0`: the achievable rate never drops below the zero baseline. -/
theorem rate_equalNoise_nonneg [Nonempty ι] {c : ℝ} (hc : 0 < c) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c)) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnc : 0 < (Fintype.card ι : ℝ) * c := mul_pos hn hc
  have h1 : (1 : ℝ) ≤ 1 + P / (Fintype.card ι * c) := by
    have : 0 ≤ P / (Fintype.card ι * c) := div_nonneg hP hnc.le
    linarith
  exact mul_nonneg (by positivity) (Real.log_nonneg h1)

/-- **The equal-noise capacity is monotone in the power budget.**  `P₁ ≤ P₂ ⟹
    C(P₁) ≤ C(P₂)`: allocating more total power never decreases the achievable rate,
    since `log(1 + P/(n·c))` increases in `P`. -/
theorem rate_equalNoise_mono_power [Nonempty ι] {c : ℝ} (hc : 0 < c)
    {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (h : P₁ ≤ P₂) :
    (Fintype.card ι : ℝ) / 2 * Real.log (1 + P₁ / (Fintype.card ι * c))
      ≤ (Fintype.card ι : ℝ) / 2 * Real.log (1 + P₂ / (Fintype.card ι * c)) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnc : 0 < (Fintype.card ι : ℝ) * c := mul_pos hn hc
  have hx1 : (0 : ℝ) < 1 + P₁ / (Fintype.card ι * c) := by
    have : 0 ≤ P₁ / (Fintype.card ι * c) := div_nonneg hP₁ hnc.le
    linarith
  have hle : 1 + P₁ / (Fintype.card ι * c) ≤ 1 + P₂ / (Fintype.card ι * c) := by
    gcongr
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hx1 hle) (by positivity)

/-- **The equal-noise capacity is antitone in the noise floor.**  For a fixed
    power budget `P ≥ 0`, raising the common noise `c₁ ≤ c₂` never increases the
    achievable rate: `C(c₂) ≤ C(c₁)`.  This is the noise-side dual of
    `rate_equalNoise_mono_power`; it holds because `P/(n·c)` decreases in `c`. -/
theorem rate_equalNoise_antitone_noise [Nonempty ι] {P : ℝ} (hP : 0 ≤ P)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) :
    (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c₂))
      ≤ (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c₁)) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc
  have hnc₂ : 0 < (Fintype.card ι : ℝ) * c₂ := mul_pos hn hc₂
  have hx2 : (0 : ℝ) < 1 + P / (Fintype.card ι * c₂) := by
    have : 0 ≤ P / (Fintype.card ι * c₂) := div_nonneg hP hnc₂.le
    linarith
  have hle : 1 + P / (Fintype.card ι * c₂) ≤ 1 + P / (Fintype.card ι * c₁) := by
    gcongr
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hx2 hle) (by positivity)

/-! ## The wideband ceiling `C ≤ P/(2c)` -/

/-- **Wideband capacity ceiling.**  For any finite number `n` of equal parallel
    Gaussian channels of noise `c > 0` sharing total power `P ≥ 0`, the equal-noise
    capacity is capped by `P/(2c)`, *independently of `n`*:
    `(n/2)·log(1 + P/(n·c)) ≤ P/(2c)`.

    This is the infinite-bandwidth (wideband) limit of the AWGN channel: no matter
    how the total power is split across identical sub-channels, the aggregate rate
    cannot exceed `P/(2c)` nats.  It follows from the elementary tangent bound
    `log u ≤ u − 1` applied to `u = 1 + P/(n·c)`. -/
theorem rate_equalNoise_le_wideband [Nonempty ι] {c : ℝ} (hc : 0 < c) {P : ℝ}
    (hP : 0 ≤ P) :
    (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c)) ≤ P / (2 * c) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcne : c ≠ 0 := hc.ne'
  have hnne : (Fintype.card ι : ℝ) ≠ 0 := hn.ne'
  have hnc : 0 < (Fintype.card ι : ℝ) * c := mul_pos hn hc
  have hu : (0 : ℝ) < 1 + P / (Fintype.card ι * c) := by
    have : 0 ≤ P / (Fintype.card ι * c) := div_nonneg hP hnc.le
    linarith
  have hlog : Real.log (1 + P / (Fintype.card ι * c)) ≤ P / (Fintype.card ι * c) := by
    have h := Real.log_le_sub_one_of_pos hu
    linarith
  calc (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c))
      ≤ (Fintype.card ι : ℝ) / 2 * (P / (Fintype.card ι * c)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = P / (2 * c) := by field_simp

/-! ## Strict positivity and the vanishing characterization -/

/-- **Strict positivity of the equal-noise capacity.**  As soon as *any* power is
    available (`P > 0`, `c > 0`), the achievable rate is strictly positive:
    `0 < (n/2)·log(1 + P/(n·c))`.  This sharpens `rate_equalNoise_nonneg` — the rate
    sits strictly above the zero baseline, since `log` of an argument exceeding `1`
    is positive. -/
theorem rate_equalNoise_pos [Nonempty ι] {c : ℝ} (hc : 0 < c) {P : ℝ} (hP : 0 < P) :
    0 < (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c)) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnc : 0 < (Fintype.card ι : ℝ) * c := mul_pos hn hc
  have h1 : (1 : ℝ) < 1 + P / (Fintype.card ι * c) := by
    have : 0 < P / (Fintype.card ι * c) := div_pos hP hnc
    linarith
  exact mul_pos (div_pos hn (by norm_num)) (Real.log_pos h1)

/-- **The equal-noise capacity vanishes exactly at zero power.**  For `c > 0` and
    `P ≥ 0`, the rate `(n/2)·log(1 + P/(n·c))` equals `0` iff `P = 0`.  Combined with
    `rate_equalNoise_nonneg` and `rate_equalNoise_pos` this pins down the capacity's
    zero set: no power ⇒ no rate, and any positive power ⇒ positive rate. -/
theorem rate_equalNoise_eq_zero_iff [Nonempty ι] {c : ℝ} (hc : 0 < c) {P : ℝ}
    (hP : 0 ≤ P) :
    (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c)) = 0 ↔ P = 0 := by
  constructor
  · intro h
    by_contra hP0
    exact (rate_equalNoise_pos hc (lt_of_le_of_ne hP (Ne.symm hP0))).ne' h
  · intro h
    subst h
    simp

/-! ## Strict power-monotonicity and concavity of the equal-noise capacity -/

/-- **Strict power-monotonicity of the equal-noise capacity.**  For `c > 0`, a
    *strict* increase in the power budget yields a *strictly* larger rate:
    `P₁ < P₂ ⟹ C(P₁) < C(P₂)`.  This sharpens `rate_equalNoise_mono_power` from `≤`
    to `<`, mirroring how `rate_equalNoise_pos` sharpens `rate_equalNoise_nonneg`:
    every extra nat of power buys strictly positive rate. -/
theorem rate_equalNoise_strictMono_power [Nonempty ι] {c : ℝ} (hc : 0 < c)
    {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (h : P₁ < P₂) :
    (Fintype.card ι : ℝ) / 2 * Real.log (1 + P₁ / (Fintype.card ι * c))
      < (Fintype.card ι : ℝ) / 2 * Real.log (1 + P₂ / (Fintype.card ι * c)) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnc : 0 < (Fintype.card ι : ℝ) * c := mul_pos hn hc
  have hx1 : (0 : ℝ) < 1 + P₁ / (Fintype.card ι * c) := by
    have : 0 ≤ P₁ / (Fintype.card ι * c) := div_nonneg hP₁ hnc.le
    linarith
  have hlt : 1 + P₁ / (Fintype.card ι * c) < 1 + P₂ / (Fintype.card ι * c) := by
    gcongr
  exact mul_lt_mul_of_pos_left (Real.log_lt_log hx1 hlt) (by positivity)

/-- **Concavity of the equal-noise capacity in the power budget.**  For `c > 0` the
    capacity `C(P) = (n/2)·log(1 + P/(n·c))` is concave on `[0, ∞)`.  This is the
    formal statement behind the classical "capacity is a concave function of power":
    it makes power time-sharing sub-optimal (a convex combination of budgets is at
    least as good as splitting time between them), and underlies the water-filling
    and rate-region arguments for parallel Gaussian channels.  The proof composes the
    concavity of `Real.log` (`strictConcaveOn_log_Ioi`) with the affine reparametrisation
    `P ↦ 1 + P/(n·c)` and the nonnegative scaling `n/2`. -/
theorem rate_equalNoise_concaveOn_power [Nonempty ι] {c : ℝ} (hc : 0 < c) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun P => (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c))) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnc : 0 < (Fintype.card ι : ℝ) * c := mul_pos hn hc
  set k := (Fintype.card ι : ℝ) * c with hk
  have hkne : k ≠ 0 := hnc.ne'
  have hN : (0 : ℝ) ≤ (Fintype.card ι : ℝ) / 2 := by positivity
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [Set.mem_Ici] at hx hy
  have hux : (0 : ℝ) < 1 + x / k := by
    have : 0 ≤ x / k := div_nonneg hx hnc.le; linarith
  have huy : (0 : ℝ) < 1 + y / k := by
    have : 0 ≤ y / k := div_nonneg hy hnc.le; linarith
  have hsum : a * (1 + x / k) + b * (1 + y / k) = 1 + (a * x + b * y) / k := by
    field_simp
    linear_combination k * hab
  have hstep : a * Real.log (1 + x / k) + b * Real.log (1 + y / k)
      ≤ Real.log (a * (1 + x / k) + b * (1 + y / k)) := by
    have := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hux)
      (Set.mem_Ioi.mpr huy) ha hb hab
    simpa only [smul_eq_mul] using this
  simp only [smul_eq_mul]
  calc a * ((Fintype.card ι : ℝ) / 2 * Real.log (1 + x / k))
        + b * ((Fintype.card ι : ℝ) / 2 * Real.log (1 + y / k))
      = (Fintype.card ι : ℝ) / 2
          * (a * Real.log (1 + x / k) + b * Real.log (1 + y / k)) := by ring
    _ ≤ (Fintype.card ι : ℝ) / 2 * Real.log (a * (1 + x / k) + b * (1 + y / k)) :=
        mul_le_mul_of_nonneg_left hstep hN
    _ = (Fintype.card ι : ℝ) / 2 * Real.log (1 + (a * x + b * y) / k) := by rw [hsum]

/-- **Strict concavity of the equal-noise capacity in the power budget.**  For `c > 0`
    the capacity `C(P) = (n/2)·log(1 + P/(n·c))` is *strictly* concave on `[0, ∞)`,
    sharpening `rate_equalNoise_concaveOn_power` from `ConcaveOn` to `StrictConcaveOn`
    (mirroring how `rate_equalNoise_strictMono_power` sharpens the monotone version).
    Strict concavity is the property that makes power time-sharing *strictly* suboptimal
    and pins down the water-filling optimum as *unique*: no nontrivial convex combination
    of two distinct budgets is matched by splitting time between them.  The affine
    reparametrisation `P ↦ 1 + P/(n·c)` is injective, so distinct budgets map to distinct
    positive arguments where `Real.log` is strictly concave (`strictConcaveOn_log_Ioi`),
    and the strictly positive scaling `n/2 > 0` preserves the strict inequality. -/
theorem rate_equalNoise_strictConcaveOn_power [Nonempty ι] {c : ℝ} (hc : 0 < c) :
    StrictConcaveOn ℝ (Set.Ici 0)
      (fun P => (Fintype.card ι : ℝ) / 2 * Real.log (1 + P / (Fintype.card ι * c))) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnc : 0 < (Fintype.card ι : ℝ) * c := mul_pos hn hc
  set k := (Fintype.card ι : ℝ) * c with hk
  have hkne : k ≠ 0 := hnc.ne'
  have hNpos : (0 : ℝ) < (Fintype.card ι : ℝ) / 2 := by positivity
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [Set.mem_Ici] at hx hy
  have hux : (0 : ℝ) < 1 + x / k := by
    have : 0 ≤ x / k := div_nonneg hx hnc.le; linarith
  have huy : (0 : ℝ) < 1 + y / k := by
    have : 0 ≤ y / k := div_nonneg hy hnc.le; linarith
  -- the injective affine reparametrisation sends `x ≠ y` to distinct positive arguments
  have hne_arg : (1 + x / k) ≠ (1 + y / k) := by
    intro h
    apply hxy
    have hk2 : x / k = y / k := by linarith
    field_simp [hkne] at hk2
    linarith
  have hsum : a * (1 + x / k) + b * (1 + y / k) = 1 + (a * x + b * y) / k := by
    field_simp
    linear_combination k * hab
  have hstep : a * Real.log (1 + x / k) + b * Real.log (1 + y / k)
      < Real.log (a * (1 + x / k) + b * (1 + y / k)) := by
    have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.mpr hux) (Set.mem_Ioi.mpr huy)
      hne_arg ha hb hab
    simpa only [smul_eq_mul] using this
  simp only [smul_eq_mul]
  calc a * ((Fintype.card ι : ℝ) / 2 * Real.log (1 + x / k))
        + b * ((Fintype.card ι : ℝ) / 2 * Real.log (1 + y / k))
      = (Fintype.card ι : ℝ) / 2
          * (a * Real.log (1 + x / k) + b * Real.log (1 + y / k)) := by ring
    _ < (Fintype.card ι : ℝ) / 2 * Real.log (a * (1 + x / k) + b * (1 + y / k)) :=
        mul_lt_mul_of_pos_left hstep hNpos
    _ = (Fintype.card ι : ℝ) / 2 * Real.log (1 + (a * x + b * y) / k) := by rw [hsum]

end ShannonWaterFilling
