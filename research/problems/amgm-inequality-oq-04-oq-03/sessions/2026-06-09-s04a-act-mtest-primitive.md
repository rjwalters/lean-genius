# Session 2026-06-09 S4a ACT — `x`-independent M-test primitive

**Researcher**: researcher-1
**Phase transition**: ACT (S2 ACT — summability) → ACT (S4a ACT — M-test primitive)
**Outcome**: 1 new proved lemma + 1 state.md correction (S3 Wallis was
already shipped).

## Goal

Discharge the next priority from `state.md`. Stale `state.md` indicated
"S3 ACT (Wallis closed form) — open, recommended next". Audit reality
before coding.

## Finding 1: S3 Wallis already shipped

Searching `proofs/Proofs/`, found `AmgmInequalityOQ04OQ03Wallis.lean`
with `wallisHalf_even` already proved:

```lean
theorem wallisHalf_even (n : ℕ) :
    wallisHalf (2 * n) = (π / 2) * ((Nat.centralBinom n : ℝ) / 4 ^ n)
```

Confirmed via git log: PR #22046 `research(amgm-inequality-oq-04-oq-03):
S3 ACT — Wallis half-period closed form (additive companion,
Docker-verified 7743 jobs)`. The state.md was stale by ~1-2 sessions.

So S3 is **complete**. The genuinely-open legs are S4 (binomial
series), S5 (uniform summability `TendstoUniformlyOn`), and S6 (DCT
discharge).

## Finding 2: S4 splits naturally into 4a + 4b + 4c

Reviewing the S2 ACT proof of `summable_hyp2F1`, the per-term bound is
`x`-dependent (`|hypCoeff n · x^n| ≤ |x|^n`). For the next legs we need
a **uniform** bound on compact subsets of `(-1, 1)`, i.e. an
`x`-independent dominating series. This factors cleanly into:

- **S4a (this session)**: `x`-independent per-term bound
  `|hypCoeff n · x^n| ≤ R^n` valid uniformly on `{x : |x| ≤ R}`.
- **S4b (next)**: M-test corollary → uniform summability on `[-R, R]`.
- **S4c (after)**: binomial series `(1-u)^(-1/2) = ∑ centralBinom n/4^n · u^n`
  (the deep analysis leg).

S4a is the prerequisite for both S4b and (ultimately) the dominated
convergence step in S6.

## S4a contribution

```lean
lemma hypCoeff_mul_pow_abs_le_of_abs_le
    (R : ℝ) (n : ℕ) (x : ℝ) (hx : |x| ≤ R) :
    |hypCoeff n * x ^ n| ≤ R ^ n := by
  have hR : 0 ≤ R := le_trans (abs_nonneg _) hx
  rw [abs_mul, abs_pow, abs_of_nonneg (hypCoeff_nonneg n)]
  calc hypCoeff n * |x| ^ n
      ≤ 1 * |x| ^ n :=
        mul_le_mul_of_nonneg_right (hypCoeff_le_one n)
          (pow_nonneg (abs_nonneg _) n)
    _ = |x| ^ n := one_mul _
    _ ≤ R ^ n := pow_le_pow_left₀ (abs_nonneg _) hx n
```

The proof chain is `|hypCoeff n · x^n| = hypCoeff n · |x|^n ≤ 1 · |x|^n
≤ R^n`. The `hR : 0 ≤ R` derivation (from `0 ≤ |x| ≤ R`) is needed for
`pow_le_pow_left₀`. Otherwise it's a clean 4-step calc.

The lemma's `R` parameter is shared across all `n` — this is exactly
what distinguishes it from `summable_hyp2F1`'s per-term-bounded version
(where the dominating series varies with `x`).

## Why this is the M-test primitive

The Weierstrass M-test states: if `|f_n(x)| ≤ M_n` for all `x` in a
domain `D` and `∑ M_n < ∞`, then `∑ f_n(x)` converges uniformly on `D`.

Here `f_n(x) = hypCoeff n · x^n`, `D = {x : |x| ≤ R}`, and the new
lemma gives `M_n = R^n`. For `R < 1`, `∑ R^n = 1/(1-R) < ∞`. So once
`R < 1` is added as a hypothesis, S4b (`Summable_geometric` + this
lemma) and S5 (`TendstoUniformlyOn`) follow with ~20-30 LOC of glue.

## Files Modified

* `proofs/Proofs/AmgmInequalityOQ04OQ03.lean`:
  * Added §7 header comment block (+8 LOC of comments).
  * Added `hypCoeff_mul_pow_abs_le_of_abs_le` lemma (+15 LOC including
    docstring).
* `research/problems/amgm-inequality-oq-04-oq-03/state.md`:
  * Corrected S3 (Wallis) status from "open, recommended next" to
    "✅ merged via #22046".
  * Added §S4a row showing this session.
  * Refined next-action plan: S4b smallest next (~20 LOC), then S4c
    deep, then S5.
* `research/problems/amgm-inequality-oq-04-oq-03/sessions/2026-06-09-s04a-act-mtest-primitive.md`
  (this file).

## Build verification

`./proofs/scripts/docker-build.sh Proofs.AmgmInequalityOQ04OQ03` —
**7745 jobs, success**. New lemma compiles cleanly. Two pre-existing
warnings (unused simp arg in `AmgmInequalityOQ04.lean` line 229; unused
variable `hk` in `AmgmInequalityOQ04OQ01.lean` line 72) are unchanged
by this PR.

## Axiom accounting

**Before this session**: 1 axiom in `AmgmInequalityOQ04OQ03.lean`:
- `ellipticK_eq_hyp2F1` (the deep series identity, multi-leg discharge
  in progress).

**After this session**: 1 axiom (unchanged). The lemma added is a
**substrate**, not a discharge.

## Significance (honest assessment)

* **Small but solid.** ~15 LOC. A primitive, not a headline result.
* **On the path.** Strictly required for S4b/S5/S6. Without an
  `x`-independent dominating bound, the Weierstrass M-test cannot
  apply.
* **State-clarifying value.** Discovers and corrects the stale state.md
  (S3 already shipped). Future researchers don't waste effort
  re-discovering S3.
* **Mathlib-name verification.** Confirms `pow_le_pow_left₀` is the
  correct name in v4.26 (Lean's `₀` convention; the un-`₀` version was
  renamed). Useful precedent for downstream proofs.

## Next Action

**S4b — Uniform summability on compact subsets**. With `S4a` in place,
the proof is essentially:

```lean
theorem summable_hyp2F1_uniform (R : ℝ) (hR : R < 1) (h0 : 0 ≤ R)
    (x : ℝ) (hx : |x| ≤ R) :
    Summable (fun n : ℕ => hypCoeff n * x ^ n) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) (summable_geometric_of_lt_one h0 hR)
  rw [Real.norm_eq_abs]
  exact hypCoeff_mul_pow_abs_le_of_abs_le R n x hx
```

~10 LOC. Note: this is actually slightly redundant with
`summable_hyp2F1` (which already gives summability for each fixed `x`
with `|x| < 1`), but the *uniform* phrasing (single dominating series
across the family) is what S5 (`TendstoUniformlyOn`) and S6 (DCT) need.

The proper next step is to skip S4b's plain `Summable` restatement and
go directly to S5 — a `TendstoUniformlyOn` statement that uses the
uniform M-bound from S4a.
