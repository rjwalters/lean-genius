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

Beyond the averages, the known bounds also force an unconditional **pointwise** obstruction
on the ratio itself:

  * `ratio_frequently_lt` / `ratio_frequently_gt` — for every `ε > 0`, the consecutive
        ratio is `< 1 + ε` infinitely often and `> 1 - ε` infinitely often, i.e.
        `liminf ≤ 1 ≤ limsup`.  The ratio **straddles 1** (`h3_ratio_straddles_one`): it
        cannot drift away from `1` on either side, so if (⋆) fails it fails only by
        oscillation.  The engine is the pair of Cesàro sign lemmas `cesaro_ge_imp` /
        `cesaro_le_imp` (a vanishing Cesàro mean cannot dominate a fixed nonzero constant).
  * `ratio_liminf_le_one` / `one_le_ratio_limsup` — the same straddle in honest
        `Filter.liminf`/`Filter.limsup` form: once the ratio is eventually two-sided bounded
        (the `[1/2, 2]` bounded-ratio leaf supplies this for `h₃`),
        `liminf_k h(k+1)/h k ≤ 1 ≤ limsup_k h(k+1)/h k`.  Hence if the ratio converges at
        all, its limit is forced to be `1` — a genuine two-sided pinch on the cluster set.

The averaged statements are proved for an arbitrary `h : ℕ → ℝ` that is **positive and polynomially
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

/- ## The ratio *straddles* 1 — an unconditional pointwise obstruction -/

/-- If a sequence's Cesàro mean tends to `0` and the sequence is *eventually* bounded
below by a constant `c`, then `c ≤ 0`.  (The finite head `∑_{k<N} a k` contributes
`O(1/K)`; the tail contributes `≥ c·(K−N)/K → c`, so a positive `c` would force the mean
to stay `≥ c > 0`.) -/
theorem cesaro_ge_imp {a : ℕ → ℝ} {c : ℝ}
    (hces : Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, a k) / K) atTop (𝓝 0))
    (hev : ∀ᶠ k in atTop, c ≤ a k) : c ≤ 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set S : ℝ := ∑ k ∈ Finset.range N, a k with hS
  -- an eventual lower bound for the Cesàro mean, tending to `c`
  have hle : ∀ᶠ K : ℕ in atTop,
      (S + c * ((K : ℝ) - N)) / K ≤ (∑ k ∈ Finset.range K, a k) / K := by
    filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with K hK hK0
    have hsplit : (∑ k ∈ Finset.range K, a k) = S + ∑ k ∈ Finset.Ico N K, a k := by
      rw [hS]; exact (Finset.sum_range_add_sum_Ico a hK).symm
    have htail : c * ((K : ℝ) - N) ≤ ∑ k ∈ Finset.Ico N K, a k := by
      have hcsum : (∑ _k ∈ Finset.Ico N K, c) ≤ ∑ k ∈ Finset.Ico N K, a k :=
        Finset.sum_le_sum fun k hk => hN k (Finset.mem_Ico.mp hk).1
      have heq : (∑ _k ∈ Finset.Ico N K, c) = c * ((K : ℝ) - N) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hK]; ring
      rwa [heq] at hcsum
    have hnum : S + c * ((K : ℝ) - N) ≤ S + ∑ k ∈ Finset.Ico N K, a k := by linarith
    rw [hsplit]
    gcongr
  -- the lower bound tends to `c`
  have hlow : Tendsto (fun K : ℕ => (S + c * ((K : ℝ) - N)) / K) atTop (𝓝 c) := by
    have hSK : Tendsto (fun K : ℕ => S / (K : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hNK : Tendsto (fun K : ℕ => c * (N : ℝ) / (K : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hsum : Tendsto (fun K : ℕ => S / (K : ℝ) + (c - c * (N : ℝ) / (K : ℝ)))
        atTop (𝓝 (0 + (c - 0))) := hSK.add (tendsto_const_nhds.sub hNK)
    rw [zero_add, sub_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with K hK0
    have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hK0.ne'
    field_simp
  exact le_of_tendsto_of_tendsto hlow hces hle

/-- Dual of `cesaro_ge_imp`: eventual upper bound `a k ≤ c` with vanishing Cesàro mean
forces `0 ≤ c`.  (Apply `cesaro_ge_imp` to `-a`.) -/
theorem cesaro_le_imp {a : ℕ → ℝ} {c : ℝ}
    (hces : Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, a k) / K) atTop (𝓝 0))
    (hev : ∀ᶠ k in atTop, a k ≤ c) : 0 ≤ c := by
  have hces' : Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, (-a k)) / K) atTop (𝓝 0) := by
    have h0 : Tendsto (fun K : ℕ => -((∑ k ∈ Finset.range K, a k) / K)) atTop (𝓝 (-0)) :=
      hces.neg
    rw [neg_zero] at h0
    refine h0.congr' ?_
    filter_upwards with K
    rw [← neg_div]
    congr 1
    simp
  have hev' : ∀ᶠ k in atTop, (-c) ≤ (-a k) := by
    filter_upwards [hev] with k hk; linarith
  have := cesaro_ge_imp hces' hev'
  linarith

/-- **Unconditional: the ratio cannot be eventually bounded above away from 1.**  For
every `ε > 0`, `h(k+1)/h k < 1 + ε` for infinitely many `k` — i.e.
`liminf_k h(k+1)/h k ≤ 1`.  If instead the ratio were eventually `≥ 1 + ε`, the log-ratios
would be eventually `≥ log(1+ε) > 0`, forcing their Cesàro mean `≥ log(1+ε) > 0`, against
`cesaro_log_ratio_tendsto_zero`. -/
theorem ratio_frequently_lt {h : ℕ → ℝ} (hb : PolyBounded h) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ k in atTop, h (k + 1) / h k < 1 + ε := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hge : ∀ᶠ k in atTop, (1 + ε) ≤ h (k + 1) / h k := by
    filter_upwards [hcon] with k hk; exact not_lt.mp hk
  have hlogge : ∀ᶠ k in atTop, Real.log (1 + ε) ≤ Real.log (h (k + 1) / h k) := by
    filter_upwards [hge] with k hk
    exact Real.log_le_log (by linarith) hk
  have hle0 := cesaro_ge_imp (cesaro_log_ratio_tendsto_zero hb) hlogge
  have hpos : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  linarith

/-- **Unconditional: the ratio cannot be eventually bounded below away from 1.**  For
every `ε` with `0 < ε < 1`, `1 - ε < h(k+1)/h k` for infinitely many `k` — i.e.
`1 ≤ limsup_k h(k+1)/h k`.  Symmetric to `ratio_frequently_lt` via `cesaro_le_imp`. -/
theorem ratio_frequently_gt {h : ℕ → ℝ} (hb : PolyBounded h) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) : ∃ᶠ k in atTop, 1 - ε < h (k + 1) / h k := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hle : ∀ᶠ k in atTop, h (k + 1) / h k ≤ 1 - ε := by
    filter_upwards [hcon] with k hk; exact not_lt.mp hk
  have hlogle : ∀ᶠ k in atTop, Real.log (h (k + 1) / h k) ≤ Real.log (1 - ε) := by
    filter_upwards [hle] with k hk
    exact Real.log_le_log (div_pos (hb.pos _) (hb.pos _)) hk
  have hge0 := cesaro_le_imp (cesaro_log_ratio_tendsto_zero hb) hlogle
  have hneg : Real.log (1 - ε) < 0 := Real.log_neg (by linarith) (by linarith)
  linarith

/- ## Filter-level `liminf ≤ 1 ≤ limsup` (the textbook straddle) -/

/-- **`liminf ≤ 1` in honest `Filter.liminf` form.**  The frequency statement
`ratio_frequently_lt` (`h(k+1)/h k < 1 + ε` infinitely often, for every `ε > 0`) is exactly
the assertion `liminf_k h(k+1)/h k ≤ 1`.  Promoting it to the genuine `Filter.liminf`
requires only that the ratio be *eventually bounded below* (so `liminf` is a real number and
not `-∞`), supplied here as `IsBoundedUnder (· ≥ ·)`.  For `h₃` this cobounded side-condition
is furnished by the `[1/2, 2]` bounded-ratio leaf (`Erdos1013BoundedRatio.lean`). -/
theorem ratio_liminf_le_one {h : ℕ → ℝ} (hb : PolyBounded h)
    (hbdd : IsBoundedUnder (· ≥ ·) atTop (fun k => h (k + 1) / h k)) :
    liminf (fun k => h (k + 1) / h k) atTop ≤ 1 := by
  set L := liminf (fun k => h (k + 1) / h k) atTop with hL
  by_contra hcon
  push_neg at hcon              -- hcon : 1 < L
  set ε : ℝ := (L - 1) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hfreq : ∃ᶠ k in atTop, h (k + 1) / h k ≤ 1 + ε :=
    (ratio_frequently_lt hb hεpos).mono fun k hk => le_of_lt hk
  have hle : L ≤ 1 + ε := by
    rw [hL]; exact Filter.liminf_le_of_frequently_le hfreq hbdd
  rw [hεdef] at hle
  linarith

/-- **`1 ≤ limsup` in honest `Filter.limsup` form.**  Dual to `ratio_liminf_le_one`: the
frequency statement `ratio_frequently_gt` gives `1 - ε < h(k+1)/h k` infinitely often for
every `0 < ε < 1`, i.e. `1 ≤ limsup_k h(k+1)/h k`.  Promotion needs the ratio *eventually
bounded above* (`limsup` a real number, not `+∞`), supplied as `IsBoundedUnder (· ≤ ·)`. -/
theorem one_le_ratio_limsup {h : ℕ → ℝ} (hb : PolyBounded h)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k => h (k + 1) / h k)) :
    1 ≤ limsup (fun k => h (k + 1) / h k) atTop := by
  set L := limsup (fun k => h (k + 1) / h k) atTop with hL
  by_contra hcon
  push_neg at hcon              -- hcon : L < 1
  set ε : ℝ := min ((1 - L) / 2) (1 / 2) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεle : ε ≤ (1 - L) / 2 := min_le_left _ _
  have hfreq : ∃ᶠ k in atTop, 1 - ε ≤ h (k + 1) / h k :=
    (ratio_frequently_gt hb hεpos hε1).mono fun k hk => le_of_lt hk
  have hle : 1 - ε ≤ L := by
    rw [hL]; exact Filter.le_limsup_of_frequently_le hfreq hbdd
  linarith

/-- **The unconditional Filter-level straddle** for any polynomially bounded positive `h`
whose consecutive ratio is eventually two-sided bounded:
`liminf_k h(k+1)/h k ≤ 1 ≤ limsup_k h(k+1)/h k`.  In particular the ratio cannot converge to
any limit other than `1`: if it converges at all, the limit is `1`. -/
theorem ratio_liminf_le_one_le_limsup {h : ℕ → ℝ} (hb : PolyBounded h)
    (hbelow : IsBoundedUnder (· ≥ ·) atTop (fun k => h (k + 1) / h k))
    (habove : IsBoundedUnder (· ≤ ·) atTop (fun k => h (k + 1) / h k)) :
    liminf (fun k => h (k + 1) / h k) atTop ≤ 1 ∧
      1 ≤ limsup (fun k => h (k + 1) / h k) atTop :=
  ⟨ratio_liminf_le_one hb hbelow, one_le_ratio_limsup hb habove⟩

/- ## The sharp corollary: any limit of the ratio is forced to be `1` -/

/-- **The unconditional pinch, in its sharpest user-facing form.**  For any polynomially
bounded positive `h`, *if* the consecutive ratio converges to some `L`, then `L = 1` — with
**no boundedness side-condition** (a convergent sequence is automatically bounded on both
sides, so the cobounded hypotheses of `ratio_liminf_le_one` / `one_le_ratio_limsup` come for
free via `Tendsto.isBoundedUnder_ge` / `isBoundedUnder_le`).  A convergent sequence has
`liminf = limsup = L`, and the straddle `liminf ≤ 1 ≤ limsup` then forces `L ≤ 1 ≤ L`.

This is the direct statement about the open (⋆): we cannot prove the ratio converges, but we
prove **unconditionally** that it *cannot converge to any value other than `1`*. -/
theorem ratio_tendsto_imp_one {h : ℕ → ℝ} (hb : PolyBounded h) {L : ℝ}
    (hlim : Tendsto (fun k => h (k + 1) / h k) atTop (𝓝 L)) : L = 1 := by
  -- a convergent sequence is bounded above and below
  have hbelow : IsBoundedUnder (· ≥ ·) atTop (fun k => h (k + 1) / h k) :=
    hlim.isBoundedUnder_ge
  have habove : IsBoundedUnder (· ≤ ·) atTop (fun k => h (k + 1) / h k) :=
    hlim.isBoundedUnder_le
  -- for a convergent sequence, liminf = limsup = L
  have hliminf : liminf (fun k => h (k + 1) / h k) atTop = L := hlim.liminf_eq
  have hlimsup : limsup (fun k => h (k + 1) / h k) atTop = L := hlim.limsup_eq
  have h1 : L ≤ 1 := by rw [← hliminf]; exact ratio_liminf_le_one hb hbelow
  have h2 : 1 ≤ L := by rw [← hlimsup]; exact one_le_ratio_limsup hb habove
  linarith

/-- **Contrapositive form.**  The consecutive ratio of a polynomially bounded positive `h`
does not converge to any value `L ≠ 1`.  So the only candidate limit is `1` — every other
value is ruled out unconditionally. -/
theorem ratio_not_tendsto_of_ne_one {h : ℕ → ℝ} (hb : PolyBounded h) {L : ℝ} (hL : L ≠ 1) :
    ¬ Tendsto (fun k => h (k + 1) / h k) atTop (𝓝 L) :=
  fun hlim => hL (ratio_tendsto_imp_one hb hlim)

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

/-- **Erdős #1013 (oq-02), unconditional straddle for `h₃`.**  For every `ε` with
`0 < ε < 1`, the consecutive ratio `h₃(k+1)/h₃(k)` is `< 1 + ε` infinitely often *and*
`> 1 - ε` infinitely often.  So `liminf ≤ 1 ≤ limsup`: the ratio cannot drift away from
`1` on either side — if (⋆) fails it can only be by oscillation, never by drift. -/
theorem h3_ratio_straddles_one (h₃ : ℕ → ℝ) (hpos : ∀ k, 0 < h₃ k)
    (hlow : ∀ᶠ (k : ℕ) in atTop, (k : ℝ) ^ 2 ≤ h₃ k)
    (hup : ∀ᶠ (k : ℕ) in atTop, h₃ k ≤ (k : ℝ) ^ 3) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (∃ᶠ k in atTop, h₃ (k + 1) / h₃ k < 1 + ε) ∧
      (∃ᶠ k in atTop, 1 - ε < h₃ (k + 1) / h₃ k) :=
  ⟨ratio_frequently_lt (polyBounded_of_h3 h₃ hpos hlow hup) hε,
    ratio_frequently_gt (polyBounded_of_h3 h₃ hpos hlow hup) hε hε1⟩

/-- **Erdős #1013 (oq-02), the Filter-level straddle for `h₃`.**  Given the two-sided
*bounded-ratio* input — the consecutive ratio is eventually `≥ m` and eventually `≤ M`
(as established, with `m = 1/2`, `M = 2`, in `Erdos1013BoundedRatio.lean`) — the honest
`Filter.liminf`/`Filter.limsup` obstruction holds:
`liminf_k h₃(k+1)/h₃ k ≤ 1 ≤ limsup_k h₃(k+1)/h₃ k`.
Consequently, should the ratio converge, its limit can only be `1` — the averaged evidence
for (⋆) is now a genuine two-sided pinch on the extreme cluster points. -/
theorem h3_ratio_liminf_le_one_le_limsup (h₃ : ℕ → ℝ) (hpos : ∀ k, 0 < h₃ k)
    (hlow : ∀ᶠ (k : ℕ) in atTop, (k : ℝ) ^ 2 ≤ h₃ k)
    (hup : ∀ᶠ (k : ℕ) in atTop, h₃ k ≤ (k : ℝ) ^ 3)
    {m M : ℝ} (hbelow : ∀ᶠ k in atTop, m ≤ h₃ (k + 1) / h₃ k)
    (habove : ∀ᶠ k in atTop, h₃ (k + 1) / h₃ k ≤ M) :
    liminf (fun k => h₃ (k + 1) / h₃ k) atTop ≤ 1 ∧
      1 ≤ limsup (fun k => h₃ (k + 1) / h₃ k) atTop := by
  have hb := polyBounded_of_h3 h₃ hpos hlow hup
  have hbddb : IsBoundedUnder (· ≥ ·) atTop (fun k => h₃ (k + 1) / h₃ k) := ⟨m, hbelow⟩
  have hbdda : IsBoundedUnder (· ≤ ·) atTop (fun k => h₃ (k + 1) / h₃ k) := ⟨M, habove⟩
  exact ratio_liminf_le_one_le_limsup hb hbddb hbdda

/-- **Erdős #1013 (oq-02), the forced-limit corollary for `h₃`.**  Purely from the known
`k² ≤ h₃(k) ≤ k³` bounds — no bounded-ratio leaf, no hypothesis on the asymptotic constant —
*if* the consecutive ratio `h₃(k+1)/h₃(k)` converges to some `L`, then `L = 1`.  Convergence
supplies its own two-sided boundedness, so this is strictly cleaner than
`h3_ratio_liminf_le_one_le_limsup` (no `m`, `M` inputs).  It is the sharpest unconditional
statement toward the open (⋆): the ratio *cannot* converge to anything but `1`. -/
theorem h3_ratio_tendsto_imp_one (h₃ : ℕ → ℝ) (hpos : ∀ k, 0 < h₃ k)
    (hlow : ∀ᶠ (k : ℕ) in atTop, (k : ℝ) ^ 2 ≤ h₃ k)
    (hup : ∀ᶠ (k : ℕ) in atTop, h₃ k ≤ (k : ℝ) ^ 3) {L : ℝ}
    (hlim : Tendsto (fun k => h₃ (k + 1) / h₃ k) atTop (𝓝 L)) : L = 1 :=
  ratio_tendsto_imp_one (polyBounded_of_h3 h₃ hpos hlow hup) hlim

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
