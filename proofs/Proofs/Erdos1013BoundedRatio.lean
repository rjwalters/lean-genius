/-
# Erdős Problem #1013 (oq-02): the *unconditional* bounded-ratio leaf

Erdős #1013 asks, among other things, whether the consecutive ratio of the
triangle-free chromatic threshold converges:

    h₃(k+1) / h₃(k) → 1.                                   (⋆)

The pointwise statement (⋆) is genuinely OPEN — see `Erdos1013UnconditionalRatio.lean`
for the `log log k` obstruction and the unconditional *averaged* forms (Cesàro /
geometric-mean / root).  The companion `Erdos1013ConstantRatio.lean` (oq-01) settles (⋆)
*conditionally* on the existence of the asymptotic constant `c`.

This file proves the remaining *tractable* unconditional fragment, the **bounded-ratio
leaf** demanded by the problem's stated goal:

    1/2  ≤  liminf h₃(k+1)/h₃(k)   ≤   limsup h₃(k+1)/h₃(k)  ≤  2.

The mechanism is a clean *sandwich transfer*.  The known two-sided window

    (½ − o(1))·k²·log k  ≤  h₃(k)  ≤  (1 + o(1))·k²·log k                  (W)

pins `h₃` between two constant multiples of a smooth scale `s(k) = k²·log k` whose
consecutive ratio tends to `1` (`Erdos1013Constant.scale_ratio_tendsto_one`, taken here
as the hypothesis `Tendsto (s(k+1)/s k) → 1`).  Whenever `a·s ≤ h ≤ b·s`
(`0 < a ≤ b`) the consecutive ratio is trapped per-term:

    (a/b)·(s(k+1)/s k)  ≤  h(k+1)/h(k)  ≤  (b/a)·(s(k+1)/s k),

so the ratio is eventually confined to any neighbourhood of `[a/b, b/a]`.  Feeding the
window (W) at every tolerance `ε` (`a = ½ − ε`, `b = 1 + ε`) and letting `ε → 0`
squeezes the confinement interval down to the sharp `[1/2, 2]`.

* `ratio_sandwich`         — the elementary per-term two-sided bound;
* `ratio_eventually_between` — for constant `(a,b)`: the ratio is eventually in
  `(a/b − ε, b/a + ε)` for every `ε > 0`;
* `h3_ratio_eventually_gt_half` / `h3_ratio_eventually_lt_two` — the sharp leaf for
  `h₃`: the ratio is eventually `> 1/2 − ε` and `< 2 + ε` for every `ε > 0`
  (equivalently `1/2 ≤ liminf ≤ limsup ≤ 2`).

The pointwise (⋆) is NOT settled here; the leaf only bounds the oscillation.  Feeding
the *conjectured* asymptotic (`a = b = c`) instead of the window collapses the interval
to the single point `1`, recovering oq-01 — so this leaf and oq-01 are the two ends of
the same sandwich.

Self-contained; no axioms beyond Lean/Mathlib foundations.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

open Filter Topology

namespace Erdos1013Bounded

/- ## The per-term sandwich -/

/-- **Per-term two-sided ratio bound.**  If `0 < a ≤ b`, `s` is positive, and the full
sandwich `a·s ≤ h ≤ b·s` holds at both `k` and `k+1`, then

    (a/b)·(s(k+1)/s k)  ≤  h(k+1)/h(k)  ≤  (b/a)·(s(k+1)/s k).

Pure positivity arithmetic. -/
theorem ratio_sandwich {h s : ℕ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ k, 0 < s k) {k : ℕ}
    (hklo : a * s k ≤ h k) (hkup : h k ≤ b * s k)
    (hk1lo : a * s (k + 1) ≤ h (k + 1)) (hk1up : h (k + 1) ≤ b * s (k + 1)) :
    (a / b) * (s (k + 1) / s k) ≤ h (k + 1) / h k ∧
      h (k + 1) / h k ≤ (b / a) * (s (k + 1) / s k) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsk : 0 < s k := hs k
  have hsk1 : 0 < s (k + 1) := hs (k + 1)
  have hhk : 0 < h k := lt_of_lt_of_le (by positivity) hklo
  have hhk1 : 0 < h (k + 1) := lt_of_lt_of_le (by positivity) hk1lo
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  have hskne : s k ≠ 0 := hsk.ne'
  constructor
  · -- lower bound
    rw [show (a / b) * (s (k + 1) / s k) = (a * s (k + 1)) / (b * s k) by
          field_simp,
        div_le_div_iff₀ (by positivity) hhk]
    nlinarith [mul_le_mul_of_nonneg_right hk1lo hhk.le,
      mul_le_mul_of_nonneg_left hkup hhk1.le]
  · -- upper bound
    rw [show (b / a) * (s (k + 1) / s k) = (b * s (k + 1)) / (a * s k) by
          field_simp,
        div_le_div_iff₀ hhk (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hk1up (by positivity : (0 : ℝ) ≤ a * s k),
      mul_le_mul_of_nonneg_left hklo (by positivity : (0 : ℝ) ≤ b * s (k + 1))]

/- ## Constant-`(a,b)` envelope: the ratio is eventually near `[a/b, b/a]` -/

/-- **Eventual confinement for a constant sandwich.**  Given a positive scale `s` with
`s(k+1)/s k → 1` and an eventual constant sandwich `a·s ≤ h ≤ b·s` (`0 < a ≤ b`), the
consecutive ratio `h(k+1)/h(k)` is eventually inside `(a/b − ε, b/a + ε)` for every
`ε > 0`.  Equivalently `a/b ≤ liminf ≤ limsup ≤ b/a`. -/
theorem ratio_eventually_between {h s : ℕ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ k, 0 < s k)
    (hsr : Tendsto (fun k => s (k + 1) / s k) atTop (𝓝 1))
    (hsand : ∀ᶠ k in atTop, a * s k ≤ h k ∧ h k ≤ b * s k) :
    ∀ ε > 0, ∀ᶠ k in atTop,
      a / b - ε < h (k + 1) / h k ∧ h (k + 1) / h k < b / a + ε := by
  intro ε hε
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have haob : 0 < a / b := by positivity
  have hboa : 0 < b / a := by positivity
  -- the sandwich also holds at the shifted index `k+1`
  have hsand1 : ∀ᶠ k in atTop, a * s (k + 1) ≤ h (k + 1) ∧ h (k + 1) ≤ b * s (k + 1) :=
    (tendsto_add_atTop_nat 1).eventually hsand
  -- pick `δ = ε·(a/b)`; the upper envelope shift is exactly `ε`, the lower has slack
  set δ : ℝ := ε * (a / b) with hδ
  have hδpos : 0 < δ := by positivity
  have hup1 : ∀ᶠ k in atTop, s (k + 1) / s k < 1 + δ :=
    hsr.eventually (Iio_mem_nhds (by linarith))
  have hlo1 : ∀ᶠ k in atTop, 1 - δ < s (k + 1) / s k :=
    hsr.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [hsand, hsand1, hup1, hlo1] with k hk hk1 hkU hkL
  obtain ⟨hklo, hkup⟩ := hk
  obtain ⟨hk1lo, hk1up⟩ := hk1
  obtain ⟨hL, hU⟩ := ratio_sandwich ha hab hs hklo hkup hk1lo hk1up
  refine ⟨?_, ?_⟩
  · -- lower: `a/b − ε < r`
    have hlt : (a / b) * (1 - δ) < (a / b) * (s (k + 1) / s k) :=
      mul_lt_mul_of_pos_left hkL haob
    have hge : a / b - ε ≤ (a / b) * (1 - δ) := by
      have hexp : (a / b) * (1 - δ) = a / b - ε * (a / b) ^ 2 := by rw [hδ]; ring
      rw [hexp]
      have hle1 : (a / b) ^ 2 ≤ 1 := by
        have : a / b ≤ 1 := (div_le_one hb).mpr hab
        nlinarith [haob.le]
      nlinarith [hε]
    linarith
  · -- upper: `r < b/a + ε`
    have hlt : (b / a) * (s (k + 1) / s k) < (b / a) * (1 + δ) :=
      mul_lt_mul_of_pos_left hkU hboa
    have heq : (b / a) * (1 + δ) = b / a + ε := by
      rw [hδ]; field_simp
    linarith

/- ## The sharp bounded-ratio leaf for `h₃` -/

/-- The window hypothesis `(½ − o(1))·s ≤ h₃ ≤ (1 + o(1))·s`, spelled out: for every
tolerance `ε > 0`, eventually `(½ − ε)·s ≤ h₃` and `h₃ ≤ (1 + ε)·s`. -/
def WindowBounds (h₃ s : ℕ → ℝ) : Prop :=
  ∀ ε > 0, (∀ᶠ k in atTop, (1 / 2 - ε) * s k ≤ h₃ k) ∧
    (∀ᶠ k in atTop, h₃ k ≤ (1 + ε) * s k)

/-- **Upper leaf.**  Under the window bounds and `s(k+1)/s k → 1`, the consecutive ratio
of `h₃` is eventually `< 2 + ε` for every `ε > 0`; i.e. `limsup h₃(k+1)/h₃(k) ≤ 2`. -/
theorem h3_ratio_eventually_lt_two {h₃ s : ℕ → ℝ} (hs : ∀ k, 0 < s k)
    (hsr : Tendsto (fun k => s (k + 1) / s k) atTop (𝓝 1))
    (hwin : WindowBounds h₃ s) :
    ∀ ε > 0, ∀ᶠ k in atTop, h₃ (k + 1) / h₃ k < 2 + ε := by
  intro ε hε
  -- window level `δ = ε/(20+2ε) ∈ (0, ½)`; then `b/a = (1+δ)/(½−δ) ≤ 2 + ε/2`
  set δ : ℝ := ε / (20 + 2 * ε) with hδdef
  have hden : (0 : ℝ) < 20 + 2 * ε := by positivity
  have hδpos : 0 < δ := by positivity
  have hδmul : δ * (20 + 2 * ε) = ε := by rw [hδdef]; field_simp
  have hδhalf : δ < 1 / 2 := by rw [hδdef, div_lt_iff₀ hden]; nlinarith
  have ha : (0 : ℝ) < 1 / 2 - δ := by linarith
  have hab : (1 : ℝ) / 2 - δ ≤ 1 + δ := by linarith
  obtain ⟨hlow, hup⟩ := hwin δ hδpos
  have hsand : ∀ᶠ k in atTop, (1 / 2 - δ) * s k ≤ h₃ k ∧ h₃ k ≤ (1 + δ) * s k :=
    hlow.and hup
  have key := ratio_eventually_between ha hab hs hsr hsand (ε / 2) (by positivity)
  have hba : (1 + δ) / (1 / 2 - δ) ≤ 2 + ε / 2 := by
    rw [div_le_iff₀ ha]; nlinarith [hδmul, hδpos, hε]
  filter_upwards [key] with k hk
  have := hk.2
  linarith [hba]

/-- **Lower leaf.**  Under the window bounds and `s(k+1)/s k → 1`, the consecutive ratio
of `h₃` is eventually `> 1/2 − ε` for every `ε > 0`; i.e. `1/2 ≤ liminf h₃(k+1)/h₃(k)`. -/
theorem h3_ratio_eventually_gt_half {h₃ s : ℕ → ℝ} (hs : ∀ k, 0 < s k)
    (hsr : Tendsto (fun k => s (k + 1) / s k) atTop (𝓝 1))
    (hwin : WindowBounds h₃ s) :
    ∀ ε > 0, ∀ᶠ k in atTop, 1 / 2 - ε < h₃ (k + 1) / h₃ k := by
  intro ε hε
  set δ : ℝ := ε / (20 + 2 * ε) with hδdef
  have hden : (0 : ℝ) < 20 + 2 * ε := by positivity
  have hδpos : 0 < δ := by positivity
  have hδmul : δ * (20 + 2 * ε) = ε := by rw [hδdef]; field_simp
  have hδhalf : δ < 1 / 2 := by rw [hδdef, div_lt_iff₀ hden]; nlinarith
  have ha : (0 : ℝ) < 1 / 2 - δ := by linarith
  have hab : (1 : ℝ) / 2 - δ ≤ 1 + δ := by linarith
  obtain ⟨hlow, hup⟩ := hwin δ hδpos
  have hsand : ∀ᶠ k in atTop, (1 / 2 - δ) * s k ≤ h₃ k ∧ h₃ k ≤ (1 + δ) * s k :=
    hlow.and hup
  have key := ratio_eventually_between ha hab hs hsr hsand (ε / 2) (by positivity)
  have hab_lower : 1 / 2 - ε / 2 ≤ (1 / 2 - δ) / (1 + δ) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + δ)]
    nlinarith [hδmul, hδpos, hε]
  filter_upwards [key] with k hk
  have := hk.1
  linarith [hab_lower]

end Erdos1013Bounded
