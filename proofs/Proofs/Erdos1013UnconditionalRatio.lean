/-
# Erdős Problem #1013 (oq-02): the *unconditional* averaged ratio statements

Erdős #1013 asks for the asymptotics of `h₃(k)` — the least number of vertices in a
triangle-free graph of chromatic number `k` — and, separately, whether the consecutive
ratio converges:

    h₃(k+1) / h₃(k) → 1.                                   (⋆)

The known bounds are

    (log k / log log k)·k²  ≪  h₃(k)  ≪  (log k)·k².

The companion file `Erdos1013ConstantRatio.lean` (oq-01) proves (⋆) *conditionally*:
if the asymptotic constant `c` with `h₃(k) ~ c·k²·log k` exists (`c > 0`), then (⋆)
follows.  The exact constant `c` is OPEN, so that route is conditional.

This file makes the **first unconditional progress** in the ratio direction.  The
pointwise statement (⋆) is genuinely OPEN — the `log log k` gap between the known upper
and lower bounds is exactly a factor that a naive squeeze of `h₃(k+1)/h₃(k)` cannot
control (see the `Remarks` at the bottom).  What the known bounds *do* give,
unconditionally, is every **averaged** form of (⋆):

  * `cesaro_log_ratio_tendsto_zero` — the Cesàro mean of the log-ratios vanishes:
        (1/K)·Σ_{k<K} log(h(k+1)/h(k)) → 0;
  * `geom_mean_ratio_tendsto_one`   — the geometric mean of the first `K` consecutive
        ratios tends to `1`:  `(h(K)/h(0))^{1/K} → 1`;
  * `root_tendsto_one`              — the root test is trivial: `h(k)^{1/k} → 1`.

All three are proved for an arbitrary `h : ℕ → ℝ` that is **positive and polynomially
sandwiched** (`PolyBounded`); the genuine `h₃`, whose bounds sit between `k²` and `k³`,
qualifies (`polyBounded_of_h3`), so the corollaries `h3_*` apply verbatim.

The single analytic engine is `log_div_tendsto_zero`:  for a polynomially bounded
positive sequence, `log(h k)/k → 0`.  Everything else is telescoping and continuity of
`exp`/`log`.

`ratio_iff_log_ratio` records that the open pointwise (⋆) is *equivalent* to the
log-ratios vanishing pointwise; this file proves only their Cesàro average vanishes,
which is strictly weaker and does not close (⋆).

Self-contained; no axioms beyond Lean/Mathlib foundations.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

open Filter Topology

namespace Erdos1013Ratio

/-- A candidate growth function is **polynomially bounded** if it is everywhere
positive, eventually bounded below by a positive constant, and eventually bounded
above by a polynomial `B·kᵈ`.  The genuine triangle-free chromatic threshold `h₃`
satisfies this because `k² ≲ h₃(k) ≲ k³` (see `polyBounded_of_h3`). -/
structure PolyBounded (h : ℕ → ℝ) : Prop where
  pos : ∀ k, 0 < h k
  lower : ∃ A : ℝ, 0 < A ∧ ∀ᶠ k in atTop, A ≤ h k
  upper : ∃ (B : ℝ) (d : ℕ), 0 < B ∧ ∀ᶠ k in atTop, h k ≤ B * (k : ℝ) ^ d

/- ## Basic limit `log k / k → 0` -/

/-- The elementary fact `log k / k → 0` (over `ℕ`), from `log =o[atTop] id`. -/
theorem log_natCast_div_tendsto_zero :
    Tendsto (fun k : ℕ => Real.log k / k) atTop (𝓝 0) := by
  have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simpa [Function.comp] using h2.comp tendsto_natCast_atTop_atTop

/- ## Analytic engine: `log(h k)/k → 0` for polynomially bounded `h` -/

/-- **The engine.**  A polynomially bounded positive sequence grows subexponentially:
`log(h k)/k → 0`.  Proof: squeeze `log(h k)/k` between `log A/k → 0` (lower constant
bound) and `(log B + d·log k)/k → 0` (upper polynomial bound). -/
theorem log_div_tendsto_zero {h : ℕ → ℝ} (hb : PolyBounded h) :
    Tendsto (fun k : ℕ => Real.log (h k) / k) atTop (𝓝 0) := by
  obtain ⟨A, hA, hlow⟩ := hb.lower
  obtain ⟨B, d, hB, hup⟩ := hb.upper
  -- lower squeeze bound `log A / k → 0`
  have hg : Tendsto (fun k : ℕ => Real.log A / k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  -- upper squeeze bound `(log B + d·log k)/k → 0`
  have hu : Tendsto (fun k : ℕ => (Real.log B + (d : ℝ) * Real.log k) / k) atTop (𝓝 0) := by
    have e1 : Tendsto (fun k : ℕ => Real.log B / k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have e2 : Tendsto (fun k : ℕ => (d : ℝ) * (Real.log k / k)) atTop (𝓝 ((d : ℝ) * 0)) :=
      tendsto_const_nhds.mul log_natCast_div_tendsto_zero
    rw [mul_zero] at e2
    have hsum := e1.add e2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hu ?_ ?_
  · -- `log A / k ≤ log(h k) / k`; `gcongr` reduces to `A ≤ h k` (`hlow`) and `0 < A` (`hA`)
    filter_upwards [hlow] with k hk
    gcongr
  · -- `log(h k) / k ≤ (log B + d·log k) / k`
    filter_upwards [hup, eventually_gt_atTop 0] with k hk hk0
    have hkd : (0 : ℝ) < (k : ℝ) ^ d := by
      have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
      positivity
    have hlogle : Real.log (h k) ≤ Real.log (B * (k : ℝ) ^ d) := Real.log_le_log (hb.pos k) hk
    have hrw : Real.log (B * (k : ℝ) ^ d) = Real.log B + (d : ℝ) * Real.log k := by
      rw [Real.log_mul hB.ne' hkd.ne', Real.log_pow]
    rw [hrw] at hlogle
    gcongr

/- ## Unconditional averaged ratio statements -/

/-- **Cesàro mean of the log-ratios vanishes** (unconditional).  For a polynomially
bounded positive sequence,
`(1/K)·Σ_{k<K} log(h(k+1)/h(k)) → 0`.  By telescoping the sum equals
`log(h K) − log(h 0)`, and each term over `K` tends to `0` by the engine. -/
theorem cesaro_log_ratio_tendsto_zero {h : ℕ → ℝ} (hb : PolyBounded h) :
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, Real.log (h (k + 1) / h k)) / K)
      atTop (𝓝 0) := by
  -- telescoping identity
  have htel : ∀ K : ℕ,
      (∑ k ∈ Finset.range K, Real.log (h (k + 1) / h k)) = Real.log (h K) - Real.log (h 0) := by
    intro K
    induction K with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Real.log_div (hb.pos _).ne' (hb.pos _).ne']
      ring
  simp_rw [htel, sub_div]
  have e1 : Tendsto (fun K : ℕ => Real.log (h K) / K) atTop (𝓝 0) := log_div_tendsto_zero hb
  have e2 : Tendsto (fun K : ℕ => Real.log (h 0) / K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa using e1.sub e2

/-- **The geometric mean of consecutive ratios tends to 1** (unconditional).  Since
`∏_{k<K} h(k+1)/h(k) = h(K)/h(0)`, this is `(h K / h 0)^{1/K} → 1` — the ratio form of
(⋆) *on average*.  Proof: `(h K/h 0)^{1/K} = exp((log h K − log h 0)/K) → exp 0 = 1`. -/
theorem geom_mean_ratio_tendsto_one {h : ℕ → ℝ} (hb : PolyBounded h) :
    Tendsto (fun K : ℕ => (h K / h 0) ^ ((K : ℝ)⁻¹)) atTop (𝓝 1) := by
  have e1 : Tendsto (fun K : ℕ => Real.log (h K) / K) atTop (𝓝 0) := log_div_tendsto_zero hb
  have e2 : Tendsto (fun K : ℕ => Real.log (h 0) / K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsub : Tendsto (fun K : ℕ => Real.log (h K) / K - Real.log (h 0) / K) atTop (𝓝 0) := by
    simpa using e1.sub e2
  have hexp :
      Tendsto (fun K : ℕ => Real.exp (Real.log (h K) / K - Real.log (h 0) / K))
        atTop (𝓝 (Real.exp 0)) := (Real.continuous_exp.tendsto 0).comp hsub
  rw [Real.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hdiv : (0 : ℝ) < h K / h 0 := div_pos (hb.pos K) (hb.pos 0)
  rw [Real.rpow_def_of_pos hdiv, Real.log_div (hb.pos K).ne' (hb.pos 0).ne']
  congr 1
  field_simp

/-- **The root test is trivially 1** (unconditional): `h(k)^{1/k} → 1` for a
polynomially bounded positive sequence.  `h(k)^{1/k} = exp(log(h k)/k) → exp 0 = 1`. -/
theorem root_tendsto_one {h : ℕ → ℝ} (hb : PolyBounded h) :
    Tendsto (fun k : ℕ => (h k) ^ ((k : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (h k) / k) atTop (𝓝 0) := log_div_tendsto_zero hb
  have hexp : Tendsto (fun k : ℕ => Real.exp (Real.log (h k) / k)) atTop (𝓝 (Real.exp 0)) :=
    (Real.continuous_exp.tendsto 0).comp hlog
  rw [Real.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards with k
  rw [Real.rpow_def_of_pos (hb.pos k), div_eq_mul_inv]

/- ## Framing the open pointwise question -/

/-- The genuinely open pointwise ratio question (⋆) is *equivalent* to the log-ratios
vanishing pointwise.  This file proves only that their **Cesàro average** vanishes
(`cesaro_log_ratio_tendsto_zero`), which is strictly weaker and does not settle (⋆). -/
theorem ratio_iff_log_ratio {h : ℕ → ℝ} (hb : PolyBounded h) :
    Tendsto (fun k => h (k + 1) / h k) atTop (𝓝 1) ↔
      Tendsto (fun k => Real.log (h (k + 1) / h k)) atTop (𝓝 0) := by
  constructor
  · intro hr
    have := (Real.continuousAt_log (one_ne_zero)).tendsto.comp hr
    simpa [Real.log_one, Function.comp] using this
  · intro hl
    have hexp : Tendsto (fun k => Real.exp (Real.log (h (k + 1) / h k))) atTop (𝓝 (Real.exp 0)) :=
      (Real.continuous_exp.tendsto 0).comp hl
    rw [Real.exp_zero] at hexp
    refine hexp.congr' ?_
    filter_upwards with k
    rw [Real.exp_log (div_pos (hb.pos _) (hb.pos _))]

/- ## Specialisation to the genuine threshold `h₃` -/

/-- The genuine triangle-free chromatic threshold (as a real candidate `h₃`) is
polynomially bounded: its known bounds place it between `k²` and `k³`, so it satisfies
`PolyBounded` with `A = 1`, `B = 1`, `d = 3`. -/
theorem polyBounded_of_h3 (h₃ : ℕ → ℝ) (hpos : ∀ k, 0 < h₃ k)
    (hlow : ∀ᶠ (k : ℕ) in atTop, (k : ℝ) ^ 2 ≤ h₃ k)
    (hup : ∀ᶠ (k : ℕ) in atTop, h₃ k ≤ (k : ℝ) ^ 3) : PolyBounded h₃ := by
  refine ⟨hpos, ⟨1, one_pos, ?_⟩, ⟨1, 3, one_pos, ?_⟩⟩
  · filter_upwards [hlow, eventually_ge_atTop 1] with k hk hk1
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    nlinarith [hk]
  · filter_upwards [hup] with k hk
    simpa using hk

/-- **Erdős #1013 (oq-02), unconditional Cesàro form for `h₃`.**  Whatever the exact
asymptotics of `h₃`, the Cesàro mean of its log-ratios vanishes. -/
theorem h3_cesaro_log_ratio_tendsto_zero (h₃ : ℕ → ℝ) (hpos : ∀ k, 0 < h₃ k)
    (hlow : ∀ᶠ (k : ℕ) in atTop, (k : ℝ) ^ 2 ≤ h₃ k)
    (hup : ∀ᶠ (k : ℕ) in atTop, h₃ k ≤ (k : ℝ) ^ 3) :
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, Real.log (h₃ (k + 1) / h₃ k)) / K)
      atTop (𝓝 0) :=
  cesaro_log_ratio_tendsto_zero (polyBounded_of_h3 h₃ hpos hlow hup)

/-- **Erdős #1013 (oq-02), unconditional geometric-mean form for `h₃`.**  The geometric
mean of the first `K` consecutive ratios `h₃(k+1)/h₃(k)` tends to `1`. -/
theorem h3_geom_mean_ratio_tendsto_one (h₃ : ℕ → ℝ) (hpos : ∀ k, 0 < h₃ k)
    (hlow : ∀ᶠ (k : ℕ) in atTop, (k : ℝ) ^ 2 ≤ h₃ k)
    (hup : ∀ᶠ (k : ℕ) in atTop, h₃ k ≤ (k : ℝ) ^ 3) :
    Tendsto (fun K : ℕ => (h₃ K / h₃ 0) ^ ((K : ℝ)⁻¹)) atTop (𝓝 1) :=
  geom_mean_ratio_tendsto_one (polyBounded_of_h3 h₃ hpos hlow hup)

/-
## Remarks — why the *pointwise* ratio (⋆) is not settled here

Writing `r_k := log(h₃ k) − (2·log k + log log k)` for the deviation of `h₃` from the
conjectured scale `k²·log k`, the pointwise ratio (⋆) is equivalent to
`r_{k+1} − r_k → 0`.  The oq-01 hypothesis "the asymptotic constant exists" forces
`r_k → log c`, hence the differences vanish.  The *known* two-sided bounds only pin `r_k`
to an interval of width `≈ log log k`, which is unbounded, so they permit `r_k` to
oscillate by `O(log log k)` between consecutive indices — enough to keep individual
ratios away from `1`.  The averaged statements above survive precisely because
telescoping cancels the oscillation: only the *endpoint* value `r_K` (of size
`o(K)`) enters `(1/K)·Σ log-ratios`.  Closing the `log log k` gap — i.e. establishing
`h₃(k) = k²·log k·k^{o(1)}` with controlled *local* variation — is the open content of
(⋆).
-/

end Erdos1013Ratio
