import Mathlib

/-
# Dini's Theorem — OQ-01-OQ-02-OQ-01: The Explicit Modulus of Uniform Convergence of xⁿ on the Compact Subinterval [0, 1−δ]

## Research Problem: dini-theorem-oq-01-oq-02-oq-01

The grandparent file `DiniTheorem.lean` studies the sharpness of Dini's compactness
hypothesis through the witness sequence `fₙ(x) = xⁿ`.  On the *non-compact* interval `[0,1)`
this sequence is continuous, antitone in `n`, and converges pointwise to the continuous
function `0`, yet **fails to converge uniformly** — and the parent
`DiniTheoremOQ01OQ02.lean` sharpened this to its extreme: the uniform error
`sup_{x∈[0,1)} xⁿ` stays *exactly* `1` for every `n`, the supremum being approached along
`x = 1 − 1/(k+1) → 1` but **never attained**.

This file answers the parent's open question OQ-01:

> Rate of approach: quantify how fast `sup_{x∈[0,1−δ]} xⁿ → 0` as the domain is shrunk to a
> compact subinterval `[0,1−δ]`, recovering uniform convergence with an explicit modulus in
> `δ` and `n`.

**Answer.**  On the compact subinterval `[0,1−δ]` (with `δ ∈ (0,1]`) everything changes:

* the supremum is **attained** at the right endpoint, `sup_{x∈[0,1−δ]} xⁿ = (1−δ)ⁿ`
  (contrast the parent's never-attained `1`);
* `(1−δ)ⁿ → 0` geometrically, so convergence **is** uniform — Dini's conclusion is
  recovered the moment compactness is restored;
* the rate is explicit: `(1−δ)ⁿ < ε` as soon as `n ≥ log ε / log(1−δ)`, i.e. with modulus
  `N(ε,δ) = ⌈log ε / log(1−δ)⌉`.

## What is proved

* `pow_le_endpoint` — `xⁿ ≤ (1−δ)ⁿ` for `x ∈ [0,1−δ]` (the endpoint dominates).
* `isGreatest_pow_image_Icc` — `(1−δ)ⁿ` is the **greatest** value of `{ xⁿ : x ∈ [0,1−δ] }`,
  i.e. the supremum is attained (at `x = 1−δ`).
* `pow_sSup_Icc` / `pow_uniform_error_Icc` — hence `sup_{x∈[0,1−δ]} xⁿ = (1−δ)ⁿ` and the
  uniform error `sup_{x∈[0,1−δ]} |xⁿ − 0| = (1−δ)ⁿ`.
* `pow_tendsto_zero` — `(1−δ)ⁿ → 0` (geometric decay).
* `pow_tendstoUniformlyOn_Icc` — the headline: `xⁿ ⇉ 0` **uniformly** on `[0,1−δ]`, the
  recovery of Dini's conclusion once compactness is restored — directly contrasting the
  parent's `pow_not_tendstoUniformlyOn_Ico_sharp`.
* `pow_lt_of_log_modulus` — the explicit modulus (real threshold): `log ε / log(1−δ) ≤ n`
  forces `(1−δ)ⁿ ≤ ε`.
* `pow_lt_of_ceil_modulus` — packaged as a concrete natural-number modulus
  `N(ε,δ) = ⌈log ε / log(1−δ)⌉`.

Tags: analysis, dini, uniform-convergence, supremum, modulus, geometric-decay, wiedijk
-/

namespace DiniTheoremOQ01OQ02OQ01

open Set Filter Topology

-- ============================================================
-- Part I: The supremum of xⁿ over [0, 1−δ] is attained, equal to (1−δ)ⁿ
-- ============================================================

/-- On the compact subinterval `[0,1−δ]` the right endpoint dominates: `xⁿ ≤ (1−δ)ⁿ`. -/
theorem pow_le_endpoint {δ : ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 - δ)) (n : ℕ) :
    x ^ n ≤ (1 - δ) ^ n :=
  pow_le_pow_left₀ hx.1 hx.2 n

/-- **The supremum is attained.**  For `δ ≤ 1`, `(1−δ)ⁿ` is the *greatest* element of
    `{ xⁿ : x ∈ [0,1−δ] }`: it lies in the set (take `x = 1−δ`) and dominates every member.

    This is the sharp contrast with the parent's `[0,1)` picture, where the supremum `1` is
    a least upper bound that is *never* attained. -/
theorem isGreatest_pow_image_Icc {δ : ℝ} (hδ1 : δ ≤ 1) (n : ℕ) :
    IsGreatest ((fun x : ℝ => x ^ n) '' Icc (0 : ℝ) (1 - δ)) ((1 - δ) ^ n) := by
  have h0 : (0 : ℝ) ≤ 1 - δ := by linarith
  constructor
  · -- `(1−δ)ⁿ` is in the image, attained at the right endpoint `x = 1−δ`.
    exact ⟨1 - δ, ⟨h0, le_refl _⟩, rfl⟩
  · -- it is an upper bound.
    rintro y ⟨x, hx, rfl⟩
    exact pow_le_endpoint hx n

/-- **The supremum equals the endpoint value** `(1−δ)ⁿ` (attained, for `δ ≤ 1`). -/
theorem pow_sSup_Icc {δ : ℝ} (hδ1 : δ ≤ 1) (n : ℕ) :
    sSup ((fun x : ℝ => x ^ n) '' Icc (0 : ℝ) (1 - δ)) = (1 - δ) ^ n :=
  (isGreatest_pow_image_Icc hδ1 n).csSup_eq

/-- **The uniform error on `[0,1−δ]` equals `(1−δ)ⁿ`.**  Since `xⁿ ≥ 0`, the error
    `|xⁿ − 0| = xⁿ`, so the error-image coincides with `{ xⁿ : x ∈ [0,1−δ] }`, whose
    supremum is the attained endpoint value `(1−δ)ⁿ`. -/
theorem pow_uniform_error_Icc {δ : ℝ} (hδ1 : δ ≤ 1) (n : ℕ) :
    sSup ((fun x : ℝ => |x ^ n - 0|) '' Icc (0 : ℝ) (1 - δ)) = (1 - δ) ^ n := by
  have himg : (fun x : ℝ => |x ^ n - 0|) '' Icc (0 : ℝ) (1 - δ)
      = (fun x : ℝ => x ^ n) '' Icc (0 : ℝ) (1 - δ) := by
    apply Set.image_congr
    intro x hx
    rw [sub_zero, abs_of_nonneg (pow_nonneg hx.1 n)]
  rw [himg]
  exact pow_sSup_Icc hδ1 n

-- ============================================================
-- Part II: Geometric decay and the recovery of uniform convergence
-- ============================================================

/-- **Geometric decay.**  For `δ ∈ (0,1]`, the endpoint value `(1−δ)ⁿ → 0` as `n → ∞`,
    because the base satisfies `0 ≤ 1−δ < 1`. -/
theorem pow_tendsto_zero {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n : ℕ => (1 - δ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

/-- **The recovery of Dini's conclusion.**  On the *compact* subinterval `[0,1−δ]`
    (`δ ∈ (0,1]`), the sequence `xⁿ` converges to `0` **uniformly** — exactly the conclusion
    that fails on the non-compact `[0,1)` (cf. the parent's
    `pow_not_tendstoUniformlyOn_Ico_sharp`).

    The proof is the rate estimate: `xⁿ ≤ (1−δ)ⁿ` uniformly in `x`, and `(1−δ)ⁿ → 0`, so the
    uniform error is eventually below any `ε > 0`. -/
theorem pow_tendstoUniformlyOn_Icc {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    TendstoUniformlyOn (fun n (x : ℝ) => x ^ n) (fun _ => (0 : ℝ)) atTop
      (Icc (0 : ℝ) (1 - δ)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- eventually `(1−δ)ⁿ < ε`.
  have hev : ∀ᶠ n : ℕ in atTop, (1 - δ) ^ n < ε :=
    (pow_tendsto_zero hδ0 hδ1).eventually (Iio_mem_nhds hε)
  filter_upwards [hev] with n hn x hx
  -- `dist 0 (xⁿ) = xⁿ ≤ (1−δ)ⁿ < ε`.
  have hx0 : (0 : ℝ) ≤ x ^ n := pow_nonneg hx.1 n
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hx0]
  calc x ^ n ≤ (1 - δ) ^ n := pow_le_endpoint hx n
    _ < ε := hn

-- ============================================================
-- Part III: The explicit modulus N(ε,δ) = ⌈log ε / log(1−δ)⌉
-- ============================================================

/-- **The explicit modulus (real threshold).**  For `δ ∈ (0,1)` and `ε > 0`, once
    `n ≥ log ε / log(1−δ)` we have `(1−δ)ⁿ ≤ ε`.

    Taking logarithms turns `(1−δ)ⁿ ≤ ε` into `n · log(1−δ) ≤ log ε`; since
    `log(1−δ) < 0` (as `0 < 1−δ < 1`), dividing by it reverses the inequality and yields the
    threshold `n ≥ log ε / log(1−δ)`. -/
theorem pow_lt_of_log_modulus {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) {n : ℕ}
    (hn : Real.log ε / Real.log (1 - δ) ≤ (n : ℝ)) :
    (1 - δ) ^ n ≤ ε := by
  set r : ℝ := 1 - δ with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  -- `n · log r ≤ log ε`.
  have hmul : (n : ℝ) * Real.log r ≤ Real.log ε :=
    (div_le_iff_of_neg hlogr).mp hn
  -- exponentiate: `rⁿ = exp(log(rⁿ)) ≤ exp(log ε) = ε`.
  have hpow_pos : (0 : ℝ) < r ^ n := pow_pos hr0 n
  rw [← Real.exp_log hpow_pos, ← Real.exp_log hε]
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow]
  exact hmul

/-- **The explicit modulus (natural-number form).**  Define `N(ε,δ) = ⌈log ε / log(1−δ)⌉`.
    Then for every `n ≥ N(ε,δ)` we have `(1−δ)ⁿ ≤ ε`.  This packages
    `pow_lt_of_log_modulus` with the standard `Nat.le_ceil` bound. -/
theorem pow_lt_of_ceil_modulus {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) {n : ℕ}
    (hn : ⌈Real.log ε / Real.log (1 - δ)⌉₊ ≤ n) :
    (1 - δ) ^ n ≤ ε := by
  apply pow_lt_of_log_modulus hδ0 hδ1 hε
  calc Real.log ε / Real.log (1 - δ)
      ≤ (⌈Real.log ε / Real.log (1 - δ)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn

#check @isGreatest_pow_image_Icc
#check @pow_sSup_Icc
#check @pow_uniform_error_Icc
#check @pow_tendstoUniformlyOn_Icc
#check @pow_lt_of_log_modulus
#check @pow_lt_of_ceil_modulus

/-
## Summary

Proved (0 sorries, 0 axioms — self-contained, imports only Mathlib):

* `pow_le_endpoint` — `xⁿ ≤ (1−δ)ⁿ` on `[0,1−δ]`.
* `isGreatest_pow_image_Icc` / `pow_sSup_Icc` — `sup_{x∈[0,1−δ]} xⁿ = (1−δ)ⁿ`, **attained**
  at the right endpoint (contrast the parent's never-attained `1` on `[0,1)`).
* `pow_uniform_error_Icc` — the uniform error `sup_{x∈[0,1−δ]} |xⁿ − 0| = (1−δ)ⁿ`.
* `pow_tendsto_zero` — geometric decay `(1−δ)ⁿ → 0`.
* `pow_tendstoUniformlyOn_Icc` — **uniform** convergence `xⁿ ⇉ 0` on `[0,1−δ]`: Dini's
  conclusion is recovered once compactness is restored.
* `pow_lt_of_log_modulus` / `pow_lt_of_ceil_modulus` — the explicit modulus
  `N(ε,δ) = ⌈log ε / log(1−δ)⌉`.

This answers `dini-theorem-oq-01-oq-02` OQ[0]: on the compact subinterval `[0,1−δ]` the
uniform error decays geometrically as `(1−δ)ⁿ` (attained, not merely a supremum), recovering
uniform convergence with the explicit modulus `⌈log ε / log(1−δ)⌉` — the precise quantitative
counterpart to the parent's never-attained boundary supremum `1` on the full `[0,1)`.
-/

end DiniTheoremOQ01OQ02OQ01
