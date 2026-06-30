import Mathlib

/-!
# Dini's Theorem: monotonicity in `n` is necessary (a moving-bump witness)

**Dini's theorem.** If `Fₙ` is a *monotone* sequence of continuous real-valued functions on a
compact space, converging pointwise to a continuous limit `f`, then the convergence is in fact
*uniform*.

The parent entry (`DiniTheorem.lean`) re-exports Dini's theorem from Mathlib and supplies two
sharpness witnesses built from `xⁿ`:

* **continuity of the limit is necessary** — `xⁿ` on `[0,1]`, whose pointwise limit jumps at
  `x = 1`;
* **compactness of the domain is necessary** — `xⁿ` on `[0,1)`.

This entry completes the trilogy by addressing the *third* hypothesis, which the parent's open
question singles out: **monotonicity in `n` is necessary**. We exhibit a smooth **moving bump**

```
  Fₙ(x) = n · x · exp(−n · x)
```

on the compact interval `[0,1]`. Each `Fₙ` is continuous; the sequence converges pointwise to the
continuous function `0`; the domain is compact — yet the convergence is **not** uniform. The bump
peaks at `x = 1/n` with height `Fₙ(1/n) = e⁻¹`, which travels left toward `0` as `n → ∞` without
shrinking in height, so `sup_x |Fₙ(x)|` stays `≥ e⁻¹`. Since the only Dini hypothesis that fails is
monotonicity (we verify the family is, concretely, neither monotone nor antitone in `n` at
`x = 1/2`), monotonicity cannot be dropped.

This is the smooth analogue of the classical "moving triangular bump"; using `n x e^{−n x}` instead
of a piecewise-linear tent keeps continuity a one-liner (`fun_prop`) and reduces the pointwise limit
to the standard fact `t · e^{−t} → 0`.
-/

open Filter Topology Set

namespace DiniTheoremOQ01OQ01

/-- The moving bump `Fₙ(x) = n · x · exp(−n · x)`. It peaks at `x = 1/n` with height `e⁻¹`. -/
noncomputable def bump (n : ℕ) (x : ℝ) : ℝ := (n : ℝ) * x * Real.exp (-((n : ℝ) * x))

/-! ## The bump satisfies all of Dini's hypotheses except monotonicity -/

/-- Each `Fₙ` is continuous. -/
theorem bump_continuous (n : ℕ) : Continuous (bump n) := by
  unfold bump; fun_prop

/-- **Pointwise convergence.** For every `x ≥ 0`, `Fₙ(x) → 0`. For `x = 0` the sequence is constantly
`0`; for `x > 0` we substitute `t = n·x → ∞` into the standard limit `t·e^{−t} → 0`. -/
theorem bump_tendsto_zero {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => bump n x) atTop (𝓝 0) := by
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0
    simp only [bump, mul_zero, zero_mul]
    exact tendsto_const_nhds
  · have hto : Tendsto (fun n : ℕ => (n : ℝ) * x) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hpos
    simpa only [bump, Function.comp, pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hto

/-- The pointwise limit `0` is continuous (the limit-continuity hypothesis of Dini holds). -/
theorem zero_continuous : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const

/-- The domain `[0,1]` is compact (the compactness hypothesis of Dini holds). -/
theorem domain_isCompact : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc

/-! ## Two numeric facts about `exp(1/2)` -/

/-- `exp(1/2) < 2`, since `exp(1/2)² = exp 1 < 2.72 < 4`. -/
theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
  nlinarith [h, hsq, hpos]

/-- `3/2 < exp(1/2)`, directly from `1 + x < exp x`. -/
theorem three_half_lt_exp_half : (3 : ℝ) / 2 < Real.exp (1 / 2) := by
  have h := Real.add_one_lt_exp (x := (1 / 2 : ℝ)) (by norm_num)
  linarith

/-! ## The bump is non-monotone in `n` at `x = 1/2` -/

/-- `F₁(1/2) = (1/2)·e^{−1/2}`. -/
theorem bump_one_eval : bump 1 (1 / 2 : ℝ) = (1 / 2) * Real.exp (-(1 / 2)) := by
  unfold bump; norm_num

/-- `F₂(1/2) = e^{−1}` (the bump peaks here: `1/2 = 1/n` with `n = 2`). -/
theorem bump_two_eval : bump 2 (1 / 2 : ℝ) = Real.exp (-1) := by
  unfold bump; norm_num

/-- `F₃(1/2) = (3/2)·e^{−3/2}`. -/
theorem bump_three_eval : bump 3 (1 / 2 : ℝ) = (3 / 2) * Real.exp (-(3 / 2)) := by
  unfold bump; norm_num

/-- The sequence *rises* from `n = 1` to `n = 2` at `x = 1/2`: `F₁(1/2) < F₂(1/2)`. -/
theorem bump_one_lt_two : bump 1 (1 / 2 : ℝ) < bump 2 (1 / 2 : ℝ) := by
  rw [bump_one_eval, bump_two_eval]
  have f1 : Real.exp (-(1 / 2)) * Real.exp 1 = Real.exp (1 / 2) := by
    rw [← Real.exp_add]; norm_num
  have f2 : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [f1, f2, exp_half_lt_two, Real.exp_pos (1 : ℝ),
    Real.exp_pos (-(1 / 2) : ℝ), Real.exp_pos (-1 : ℝ)]

/-- The sequence *falls* from `n = 2` to `n = 3` at `x = 1/2`: `F₃(1/2) < F₂(1/2)`. -/
theorem bump_three_lt_two : bump 3 (1 / 2 : ℝ) < bump 2 (1 / 2 : ℝ) := by
  rw [bump_three_eval, bump_two_eval]
  have g1 : Real.exp (-(3 / 2)) * Real.exp (3 / 2) = 1 := by
    rw [← Real.exp_add]; norm_num
  have g2 : Real.exp (-1 : ℝ) * Real.exp (3 / 2) = Real.exp (1 / 2) := by
    rw [← Real.exp_add]; norm_num
  nlinarith [g1, g2, three_half_lt_exp_half, Real.exp_pos (3 / 2 : ℝ),
    Real.exp_pos (-(3 / 2) : ℝ), Real.exp_pos (-1 : ℝ)]

/-- **Non-monotonicity.** At `x = 1/2` the sequence `n ↦ Fₙ(1/2)` is neither monotone (it falls
`2 → 3`) nor antitone (it rises `1 → 2`). This is exactly the Dini hypothesis that fails. -/
theorem bump_not_monotone :
    ¬ Monotone (fun n : ℕ => bump n (1 / 2)) ∧ ¬ Antitone (fun n : ℕ => bump n (1 / 2)) := by
  constructor
  · intro hmono
    have h := hmono (show (2 : ℕ) ≤ 3 by norm_num)
    have := bump_three_lt_two
    simp only at h
    linarith
  · intro hanti
    have h := hanti (show (1 : ℕ) ≤ 2 by norm_num)
    have := bump_one_lt_two
    simp only at h
    linarith

/-! ## Yet the convergence is not uniform -/

/-- **Sharpness witness (monotonicity in `n` is necessary).** On the compact interval `[0,1]` the
moving bump `Fₙ(x) = n·x·e^{−n·x}` is continuous, converges pointwise to the continuous function `0`,
and the domain is compact — all of Dini's hypotheses except monotonicity. Yet it does **not**
converge uniformly: for every `n ≥ 1` the point `x = 1/n` lies in `[0,1]` and `Fₙ(1/n) = e⁻¹ > 1/3`,
so the uniform error never drops below `1/3`. -/
theorem bump_not_tendstoUniformlyOn :
    ¬ TendstoUniformlyOn bump (fun _ => (0 : ℝ)) atTop (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  push_neg
  refine ⟨1 / 3, by norm_num, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨N + 1, le_self_add, ?_⟩
  have hmpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  have hmge : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  -- the travelling peak `x = 1/(N+1)` lies in `[0,1]` and has height `e⁻¹`
  refine ⟨1 / ((N + 1 : ℕ) : ℝ), ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one hmpos]; exact hmge
  · have hval : bump (N + 1) (1 / ((N + 1 : ℕ) : ℝ)) = Real.exp (-1) := by
      have hcancel : ((N + 1 : ℕ) : ℝ) * (1 / ((N + 1 : ℕ) : ℝ)) = 1 := by
        field_simp
      unfold bump
      rw [hcancel, one_mul]
    rw [hval, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)]
    -- remaining goal: `1/3 ≤ exp(-1)`, equivalently `exp 1 < 3`
    have hpos := Real.exp_pos (1 : ℝ)
    have hpos' := Real.exp_pos (-1 : ℝ)
    have h3 : Real.exp 1 < 3 := by nlinarith [Real.exp_one_lt_d9]
    have hmul : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [hmul, h3, hpos, hpos', mul_pos hpos' (by linarith : (0 : ℝ) < 3 - Real.exp 1)]

/-! ## Capstone: all Dini hypotheses but monotonicity, no uniform convergence -/

/-- **The moving bump is a complete sharpness witness for the monotonicity hypothesis of Dini's
theorem.** Every hypothesis holds except monotonicity in `n`, and uniform convergence fails. -/
theorem bump_witness :
    (∀ n, Continuous (bump n)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Tendsto (fun n => bump n x) atTop (𝓝 0)) ∧
      Continuous (fun _ : ℝ => (0 : ℝ)) ∧
      IsCompact (Icc (0 : ℝ) 1) ∧
      ¬ Monotone (fun n : ℕ => bump n (1 / 2)) ∧
      ¬ Antitone (fun n : ℕ => bump n (1 / 2)) ∧
      ¬ TendstoUniformlyOn bump (fun _ => (0 : ℝ)) atTop (Icc (0 : ℝ) 1) :=
  ⟨bump_continuous, fun _ hx => bump_tendsto_zero hx.1, zero_continuous, domain_isCompact,
    bump_not_monotone.1, bump_not_monotone.2, bump_not_tendstoUniformlyOn⟩

end DiniTheoremOQ01OQ01
