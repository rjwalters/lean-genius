# Session 2026-06-09 S4b ACT — M-test packaging + Summable on closed ball

**Researcher**: researcher-5
**Phase transition**: S4a ACT (M-test primitive) → S4b ACT (M-test packaging
+ Summable corollary)
**Outcome**: 2 new proved theorems, 0 new axioms, 0 new sorries, ~30 LOC.

## Goal

Discharge the next priority from `state.md` — **S4b: Uniform summability
on compact subsets via M-test (~20 LOC, straightforward)**. The S4a
session shipped the `x`-independent per-term bound
`hypCoeff_mul_pow_abs_le_of_abs_le`; S4b consumes it via the Weierstrass
M-test setup.

## S4b deliverables

Added §8 to `Proofs/AmgmInequalityOQ04OQ03.lean`:

### 1. `summable_hyp2F1_on_closedBall`

```lean
theorem summable_hyp2F1_on_closedBall
    (R : ℝ) (hR : R < 1) (x : ℝ) (hx : |x| ≤ R) :
    Summable (fun n : ℕ => hypCoeff n * x ^ n)
```

Conclusion matches `summable_hyp2F1` (§6), but the **proof path is
different**: §6 dominates by `|x|^n` (per-`x`), §8 dominates by `R^n`
(uniform). The structural payoff is that the dominating series is
*independent of `x`* — exactly the M-test setup.

Proof: `Summable.of_norm` + `Summable.of_nonneg_of_le` with
`summable_geometric_of_lt_one hRnn hR` as the dominating series and
S4a's `hypCoeff_mul_pow_abs_le_of_abs_le` as the bound. ~8 LOC.

### 2. `hyp2F1_mtest_inputs_on_closedBall`

```lean
theorem hyp2F1_mtest_inputs_on_closedBall
    (R : ℝ) (hR : R < 1) (hRnn : 0 ≤ R) :
    Summable (fun n : ℕ => R ^ n) ∧
      ∀ (n : ℕ) (x : ℝ), x ∈ {y : ℝ | |y| ≤ R} →
        ‖hypCoeff n * x ^ n‖ ≤ R ^ n
```

Bundles the two Weierstrass-M-test hypotheses on the closed ball
`{x : |x| ≤ R}`:
(a) `∑ R^n` is summable (since `R < 1`),
(b) the per-term uniform bound `‖hypCoeff n · x^n‖ ≤ R^n` holds for
    every `x` with `|x| ≤ R`.

This is exactly the data consumed by Mathlib's `tendstoUniformlyOn_tsum`.
Packaging it as a single lemma keeps the S5 (TendstoUniformlyOn) step
mechanical: just feed the two halves into `tendstoUniformlyOn_tsum`.

Proof: `summable_geometric_of_lt_one` + S4a wrapped via `Real.norm_eq_abs`.
~6 LOC.

## Why split this way

Originally S4b was sketched as "Summable + wrap as TendstoUniformlyOn".
Splitting it into (i) the per-`x` Summable corollary that *factors
through* the uniform bound, and (ii) the M-test input lemma, keeps each
deliverable small (~8 LOC each) and isolates the TendstoUniformlyOn
step (which depends on Mathlib's M-test lemma name and signature) for
its own session. If Mathlib's `tendstoUniformlyOn_tsum` signature
turns out to differ in v4.26.0, the M-test inputs are still useful as
a standalone packaging.

## Build outcome

Docker-verified (`./proofs/scripts/docker-build.sh
Proofs.AmgmInequalityOQ04OQ03`). 0 sorries, 0 new axioms.

## What's left

| Stage | Status |
|---|---|
| S4a (M-test primitive) | ✅ shipped |
| **S4b (M-test packaging + Summable corollary)** | **✅ this session** |
| S5 ACT (TendstoUniformlyOn on compacta) | ⏳ open, ~10-20 LOC |
| S4c (binomial series for (1-u)^(-1/2)) | ⏳ open, deep (~80-150 LOC) |
| S6 ACT (DCT interchange + axiom discharge) | ⏳ deepest, multi-hundred LOC |

S5 should now be near-mechanical: feed
`hyp2F1_mtest_inputs_on_closedBall` into `tendstoUniformlyOn_tsum`
(Mathlib's M-test lemma), then verify the tsum form equals `hyp2F1` (rfl).
