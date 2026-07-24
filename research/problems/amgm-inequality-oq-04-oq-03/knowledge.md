# Knowledge Base: amgm-inequality-oq-04-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

Target: Gauss's AGM theorem M(a,b) = a·π/(2·K(k')), k = b/a, k' = √(1−k²), via the
hypergeometric representation of the complete elliptic integral of the first kind:

  K(k) = (π/2)·₂F₁(1/2, 1/2; 1; k²) = (π/2)·∑_{n≥0} cₙ k^{2n}.

`K` is already defined rigorously (interval integral) in the companion file
`AmgmInequalityOQ04OQ01.lean`, where the AGM↔K connection is itself an axiom.

---

## Insights

- The series coefficient is cₙ = ((1/2)_n / n!)² = (centralBinom n / 4ⁿ)², using the
  identity (1/2)_n / n! = (2n choose n)/4ⁿ.
- Classical expansion: K(k) = (π/2)[1 + (1/2)²k² + (1·3/(2·4))²k⁴ + ⋯]; so c₀ = 1 and
  c₁ = (1/2)² = 1/4. Both verified in Lean (`hypCoeff_zero`, `hypCoeff_one`).
- Proof route for the full identity: binomial series (1−u)^(−1/2) = ∑ (centralBinom n/4ⁿ) uⁿ,
  substitute u = k² sin²θ, integrate term by term over [0, π/2], and use the Wallis integral
  ∫₀^{π/2} sin^{2n}θ dθ = (π/2)(2n choose n)/4ⁿ.
- The k = 0 case is provable WITHOUT the deep identity: K(0) = π/2 (`ellipticK_zero`) and
  ₂F₁(…;0) = 1 (`hyp2F1_zero`), so both sides equal π/2
  (`ellipticK_hyp2F1_consistent_zero`). This anchors the axiom's correctness at k = 0.
- **Wallis half-period structural fact (S3)**: Mathlib's `integral_sin_pow_even`
  and `Real.Wallis.W` cover [0, π], not [0, π/2]. The half-period closed form
  is NOT packaged directly. Fix: apply the reduction `integral_sin_pow` (a, b
  parameterised) at a=0, b=π/2 — both boundary terms `sin a^(n+1)·cos a` and
  `sin b^(n+1)·cos b` vanish (`sin 0 = 0`, `cos(π/2) = 0`), yielding the
  clean recurrence W(n+2) = ((n+1)/(n+2)) · W(n).
- **Central binomial recurrence threading**: closed form
  W(2n) = (π/2)·centralBinom n / 4^n proved by induction using
  `Nat.succ_mul_centralBinom_succ`:
  `(n+1) · centralBinom (n+1) = 2 · (2n+1) · centralBinom n`. After casting to
  ℝ and substituting centralBinom(k+1) = 2(2k+1)·centralBinom(k) / (k+1),
  `field_simp; ring` closes the algebraic step cleanly.

## Built (across sessions, Proofs/AmgmInequalityOQ04OQ03*.lean — builds clean, 0 sorries)

In `Proofs/AmgmInequalityOQ04OQ03.lean` (S1, merged):
- `hypCoeff`, `hyp2F1` definitions (central-binomial series).
- `hypCoeff_zero` (=1), `hypCoeff_one` (=1/4), `hypCoeff_nonneg`, `hypCoeff_pos`.
- `hyp2F1_zero` : ₂F₁(…;0) = 1 (via `tsum_eq_single`).
- `ellipticK_hyp2F1_consistent_zero` : K(0) = (π/2)·₂F₁(…;0), independent of the axiom.
- `ellipticK_eq_hyp2F1` (axiom) : K(k) = (π/2)·₂F₁(1/2,1/2;1;k²) for |k|<1.

In `Proofs/AmgmInequalityOQ04OQ03.lean` summability section (S2, PR #22021 open mergeable):
- `centralBinom_le_four_pow` : Nat.centralBinom n ≤ 4^n (upper-bound gap in v4.26.0).
- `hypCoeff_le_one` : hypCoeff n ≤ 1 (direct corollary).
- `summable_hyp2F1` : Summable (fun n => hypCoeff n · x^n) for |x| < 1 (comparison
  with geometric).

In `Proofs/AmgmInequalityOQ04OQ03Wallis.lean` (S3 ACT, prior, additive companion):
- `wallisHalf n := ∫ θ in 0..π/2, sin θ ^ n` (definition).
- `wallisHalf_zero` : W(0) = π/2.
- `wallisHalf_recurrence` : W(n+2) = ((n+1)/(n+2)) · W(n) (half-period reduction).
- `wallisHalf_even` : W(2n) = (π/2) · centralBinom n / 4^n (main Wallis closed form).

In §7 of `Proofs/AmgmInequalityOQ04OQ03.lean` (S4a ACT, prior):
- `hypCoeff_mul_pow_abs_le_of_abs_le (R : ℝ) (n : ℕ) (x : ℝ) (hx : |x| ≤ R) :
   |hypCoeff n · x^n| ≤ R^n` — the `x`-independent per-term M-test bound.

In §8 of `Proofs/AmgmInequalityOQ04OQ03.lean` (S4b ACT, this session):
- `summable_hyp2F1_on_closedBall (R : ℝ) (hR : R < 1) (x : ℝ) (hx : |x| ≤ R) :
   Summable (fun n => hypCoeff n · x^n)` — per-`x` summability via the
   uniform R^n dominating series. Conclusion matches §6 but the proof
   factors through the uniform bound.
- `hyp2F1_mtest_inputs_on_closedBall (R : ℝ) (hR : R < 1) (hRnn : 0 ≤ R) :
   Summable (fun n => R^n) ∧ ∀ n x, |x| ≤ R → ‖hypCoeff n · x^n‖ ≤ R^n`
   — bundled Weierstrass-M-test hypotheses, exactly the inputs Mathlib's
   `tendstoUniformlyOn_tsum` consumes.

---

## Dead Ends / Blockers

- No general Gauss hypergeometric ₂F₁ in Mathlib.
- No off-the-shelf term-by-term integration lemma matching K; the sum/integral interchange
  (dominated convergence, delicate as k → 1) is the genuine obstacle to discharging the axiom.
- Mathlib's `integral_sin_pow_even` and `Real.Wallis.W` are over the full period [0, π]; the
  half-period closed form needed for the elliptic substitution u = k² sin²θ over [0, π/2]
  must be derived from the reduction formula directly. The S3 companion now ships this leg.

---

## Leg-by-leg axiom discharge plan

To prove `ellipticK_eq_hyp2F1 : K(k) = (π/2) · ₂F₁(1/2, 1/2; 1; k²)`:

1. ✅ **Summability** (S2, `summable_hyp2F1` in PR #22021): the series ∑ cₙ x^n
   converges for |x|<1.
2. ✅ **Wallis closed form** (S3, `wallisHalf_even`, this session): the half-period
   integral ∫₀^{π/2} sin^{2n}θ dθ has the explicit central-binomial value.
3. ✅ **Binomial series** (S6, 2026-07-24, §10): (1−u)^(−1/2) = ∑ (centralBinom n / 4ⁿ) uⁿ
   for |u|<1 — `hasSum_inv_sqrt_one_sub`, plus `hasSum_ellipticIntegrand` landing it
   pointwise on the K integrand at u = k²sin²θ. Consumed from Mathlib's
   `Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero` (a = 1/2; the module
   `Mathlib.Analysis.Analytic.Binomial` is NEW at the v4.31 pin). Coefficient identity
   `Ring.choose (1/2 + n − 1) n = centralBinom n / 4ⁿ` via
   `Ring.factorial_nsmul_multichoose_eq_ascPochhammer` +
   `Polynomial.ascPochhammer_smeval_eq_eval` + the `succ_mul_centralBinom_succ` induction.
4. ✅ **Uniform summability** (S4a/b M-test inputs; S5 `TendstoUniformlyOn` wrap +
   continuity of hyp2F1 on the open unit ball, §9).
5. ⏳ **Sum/integral interchange** (the ONLY remaining leg): all terms nonneg for
   0 ≤ k² < 1, so Beppo Levi (`MeasureTheory.integral_tsum` after
   intervalIntegral → set-integral conversion) or
   `hasSum_integral_of_dominated_convergence` computes K(k) term by term; then
   `wallisHalf_even` (leg 2) + `hypCoeff_eq_sq` assemble (π/2)·hyp2F1(k²) and the
   axiom `ellipticK_eq_hyp2F1` becomes a theorem.

The companion files in `Proofs/AmgmInequalityOQ04OQ03*.lean` are built so that legs
can ship independently without rebasing on each other; the final composition step
(leg 5) integrates them — legs 1–4 are now all in place.

## Session S6 gotchas (v4.31 pin)

- Factorial notation `n !` no longer parses (expects no space); use `n.factorial`.
- `EMetric.ball` / `EMetric.mem_ball` deprecated → `Metric.eball` / `Metric.mem_eball`;
  membership proof shape: `rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero]`
  then `ENNReal.ofReal_lt_one.mpr`.
- `HasFPowerSeriesOnBall.hasSum` + `FormalMultilinearSeries.ofScalars_apply_eq` +
  a coefficient rewrite + `Real.sqrt_eq_rpow` is the full consumption pattern for
  Mathlib power-series lemmas stated with `.ofScalars`.
