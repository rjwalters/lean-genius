# Research State: amgm-inequality-oq-04-oq-03

## Current State
**Phase**: ACT
**Path**: fast
**Since**: 2026-06-01 (S2 ACT — researcher-1) → 2026-06-09 (S4b ACT, this session)
**Iteration**: 5

## Current Focus

S4b ACT (this session, researcher-5, 2026-06-09) consumes S4a's
`x`-independent per-term bound to produce the **M-test packaging on
closed balls** for the hypergeometric series:

```
summable_hyp2F1_on_closedBall (R : ℝ) (hR : R < 1) (x : ℝ) (hx : |x| ≤ R) :
    Summable (fun n : ℕ => hypCoeff n * x ^ n)

hyp2F1_mtest_inputs_on_closedBall (R : ℝ) (hR : R < 1) (hRnn : 0 ≤ R) :
    Summable (fun n : ℕ => R ^ n) ∧
      ∀ (n : ℕ) (x : ℝ), x ∈ {y : ℝ | |y| ≤ R} →
        ‖hypCoeff n * x ^ n‖ ≤ R ^ n
```

`summable_hyp2F1_on_closedBall` matches `summable_hyp2F1` (§6) in
conclusion but the **proof path goes through the uniform dominating
series `R^n`** (rather than the per-`x` series `|x|^n`). The bundled
M-test inputs lemma packages exactly the two hypotheses Mathlib's
`tendstoUniformlyOn_tsum` consumes — making S5 (TendstoUniformlyOn)
a near-mechanical wrap.

Strictly additive — 2 new lemmas, ~30 LOC including docstrings. Zero
new axioms; zero new sorries. Docker-verified.

## Prior focus (S4a, researcher-1, 2026-06-09)

S4a ACT added the **`x`-independent per-term M-test bound**:
`hypCoeff_mul_pow_abs_le_of_abs_le (R : ℝ) (n : ℕ) (x : ℝ)
    (hx : |x| ≤ R) : |hypCoeff n * x^n| ≤ R^n`. This is a uniform
bound across the compact set `{x : |x| ≤ R}` — in contrast to
`summable_hyp2F1`'s per-term bound `|hypCoeff n · x^n| ≤ |x|^n`,
which depends on the chosen `x`. Provides the M-test primitive S4b
consumes.

## Discovery: S3 Wallis closed form ALREADY SHIPPED (correcting prior state)

Stale state.md indicated `S3 ACT (Wallis closed form)` was the next
recommended discharge leg. **In fact `wallisHalf_even` was merged
2026-06-XX via PR #22046** in `AmgmInequalityOQ04OQ03Wallis.lean`:

```
wallisHalf_even (n : ℕ) :
    wallisHalf (2 * n) = (π / 2) * ((Nat.centralBinom n : ℝ) / 4 ^ n)
```

So S3 was discharged by a prior researcher. State.md updated this session
to reflect the actual status. This frees S4a/b (binomial series) as the
next genuine open leg.

## Active Approach

Power-series realization of ₂F₁ with central-binomial coefficients
cₙ = (centralBinom n / 4ⁿ)², built on the rigorous ellipticK from
oq-04-oq-01. Leg-by-leg buildup:

- §6 (S2 ACT, prior): per-term `|x|`-dependent bound +
  `summable_hyp2F1`.
- §7 (S4a ACT, prior, researcher-1): per-term **`x`-independent** bound
  on compact subsets via `hypCoeff_mul_pow_abs_le_of_abs_le`. M-test
  primitive.
- §8 (S4b ACT, this session, researcher-5): M-test packaging on closed
  balls — `summable_hyp2F1_on_closedBall` (per-`x` Summable via the
  uniform dominating series `R^n`) + `hyp2F1_mtest_inputs_on_closedBall`
  (bundled `(Summable R^n, uniform bound)` data exactly fitting
  Mathlib's `tendstoUniformlyOn_tsum`).

## Per-stage status

| Stage | Type | Anchor PR | Status |
|---|---|---|---|
| S1 ACT (scaffold) | Lean | #20885 | ✅ merged 2026-05-29 (158 LOC, 1 axiom) |
| S2 ACT (summability) | Lean | (PR after #20885) | ✅ shipped — `summable_hyp2F1`, +64 LOC, 0 new axioms |
| S3 ACT (Wallis closed form) | Lean | #22046 | ✅ merged — `wallisHalf_even` (companion file `…Wallis.lean`) |
| S4a ACT (M-test primitive) | Lean | (prior session) | ✅ shipped — `hypCoeff_mul_pow_abs_le_of_abs_le`, +15 LOC, 0 new axioms |
| **S4b ACT (M-test packaging + Summable corollary)** | **Lean** | **(this session)** | **✅ shipped — `summable_hyp2F1_on_closedBall` + `hyp2F1_mtest_inputs_on_closedBall`, +30 LOC, 0 new axioms** |
| S4c ACT (binomial series for (1-u)^(-1/2)) | Lean | — | ⏳ open, deepest (~80-150 LOC) |
| S5 ACT (TendstoUniformlyOn on compacta) | Lean | — | ⏳ open, ~10-20 LOC (one-liner wrap via Mathlib's `tendstoUniformlyOn_tsum` + the S4b inputs) |
| S6 ACT (DCT interchange + axiom discharge) | Lean | — | ⏳ deep, depends on S3 + S4c + S5 |

## Attempt Count
- Total attempts: 5
- Current approach attempts: 4
- Approaches tried: 1

## Blockers
- No general ₂F₁ in Mathlib; no packaged term-by-term integration lemma for K.
- S4c (binomial series `(1-u)^(-1/2) = ∑ centralBinom n / 4^n · u^n`):
  requires Newton's generalized binomial theorem at `α = -1/2`. Mathlib
  has `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` and `Mathlib.Analysis.SpecialFunctions.Pow`
  but no `(1-u)^α = ∑ (α choose n) · u^n` for non-integer `α` packaged
  directly. Likely requires building from `Mathlib.Analysis.SpecificLimits`
  scaffolding + the central-binomial identity `(-1/2 choose n) =
  (-1)^n · centralBinom n / 4^n` (provable but ~20 LOC).

## Next Action

**Post-S4b priority order:**

1. **S5 ACT — `TendstoUniformlyOn` for partial sums on closed ball.**
   With S4b's `hyp2F1_mtest_inputs_on_closedBall` packaging the two
   M-test hypotheses, this should be ~5-15 LOC: feed the two halves
   into Mathlib's `tendstoUniformlyOn_tsum` (in
   `Analysis.NormedSpace.FunctionSeries`) and check the tsum form
   matches `hyp2F1` (likely `rfl`). Output along
   `atTop : Filter (Finset ℕ)`; optionally compose with
   `Finset.range` for a `Filter ℕ` version.

2. **S4c — Binomial series identity.** Mathematical core:
   `(1 - u)^(-1/2) = ∑ centralBinom n / 4^n · u^n` for `|u| < 1`. Likely
   ~80-150 LOC. The harder of the remaining legs; build incrementally
   via per-degree power-series equality.

3. **S6 ACT (deep)** — combine §3 Wallis + S4c binomial series + S5
   uniform summability via DCT to discharge the
   `ellipticK_eq_hyp2F1` axiom. Multi-hundred LOC, deferred.

**Recommendation**: S5 next (one-liner via Mathlib's M-test), then S4c
(genuine analysis work), then S6.

## Sessions

- **S1 ACT** (2026-05-29, researcher-?, PR #20885): Lean +158 LOC —
  initial scaffold. Defines `hypCoeff`, `hyp2F1`, proves c₀=1, c₁=1/4,
  cₙ>0, ₂F₁(…;0)=1, k=0 consistency check. Axiomatizes
  `ellipticK_eq_hyp2F1`.
- **S2 ACT** (2026-06-01, researcher-1): Lean +64 LOC —
  `centralBinom_le_four_pow` (mathlib gap-filler) + `hypCoeff_le_one`
  + `summable_hyp2F1`. Closes the per-term-bounded summability leg.
  See `sessions/2026-06-01-s02-act-summability.md`.
- **S3 ACT** (2026-06-XX, researcher-?, PR #22046): Lean +100 LOC in
  companion file `AmgmInequalityOQ04OQ03Wallis.lean` — `wallisHalf`,
  `wallisHalf_zero`, `wallisHalf_recurrence`, `wallisHalf_even` (the
  Wallis closed form for even powers).
- **S4a ACT** (2026-06-09, researcher-1): Lean +15 LOC —
  `hypCoeff_mul_pow_abs_le_of_abs_le`. `x`-independent M-test
  primitive on compact subsets of `(-1, 1)`. See
  `sessions/2026-06-09-s04a-act-mtest-primitive.md`.
- **S4b ACT** (2026-06-09, researcher-5, this session): Lean +30 LOC —
  `summable_hyp2F1_on_closedBall` (per-`x` Summable via the *uniform*
  dominating series `R^n`, in contrast to §6's per-`x` `|x|^n`) and
  `hyp2F1_mtest_inputs_on_closedBall` (bundled M-test data exactly
  fitting Mathlib's `tendstoUniformlyOn_tsum`). See
  `sessions/2026-06-09-s04b-act-mtest-summable.md`.
