# Research State: amgm-inequality-oq-04-oq-03

## Current State
**Phase**: ACT
**Path**: fast
**Since**: 2026-06-01 (S2 ACT — researcher-1) → 2026-06-09 (S4a ACT, this session)
**Iteration**: 4

## Current Focus

S4a ACT (this session, researcher-1, 2026-06-09) adds the
**`x`-independent per-term M-test bound** for the hypergeometric series,
`hypCoeff_mul_pow_abs_le_of_abs_le`:

```
hypCoeff_mul_pow_abs_le_of_abs_le (R : ℝ) (n : ℕ) (x : ℝ)
    (hx : |x| ≤ R) : |hypCoeff n * x^n| ≤ R^n
```

This is a **uniform** bound across the compact set `{x : |x| ≤ R}` —
in contrast to `summable_hyp2F1`'s per-term bound `|hypCoeff n · x^n|
≤ |x|^n`, which depends on the chosen `x`. The new bound provides the
M-test primitive needed to extend `summable_hyp2F1` to a
`TendstoUniformlyOn` statement (S5 ACT) on compact subsets of `(-1, 1)`,
which is in turn an input to the eventual term-by-term integration step
of the discharge of `ellipticK_eq_hyp2F1` (S6 ACT).

Strictly a primitive — 1 new lemma, ~15 LOC including docstring. Zero
new axioms; zero new sorries. Docker-verified.

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
- §7 (S4a ACT, this session): per-term **`x`-independent** bound on
  compact subsets via `hypCoeff_mul_pow_abs_le_of_abs_le`. M-test
  primitive.

## Per-stage status

| Stage | Type | Anchor PR | Status |
|---|---|---|---|
| S1 ACT (scaffold) | Lean | #20885 | ✅ merged 2026-05-29 (158 LOC, 1 axiom) |
| S2 ACT (summability) | Lean | (PR after #20885) | ✅ shipped — `summable_hyp2F1`, +64 LOC, 0 new axioms |
| S3 ACT (Wallis closed form) | Lean | #22046 | ✅ merged — `wallisHalf_even` (companion file `…Wallis.lean`) |
| **S4a ACT (M-test primitive)** | **Lean** | **(this session)** | **✅ shipped — `hypCoeff_mul_pow_abs_le_of_abs_le`, +15 LOC, 0 new axioms** |
| S4b ACT (uniform summability) | Lean | — | ⏳ open, smallest next leg (~20 LOC; uses S4a + `summable_geometric_of_lt_one`) |
| S4c ACT (binomial series for (1-u)^(-1/2)) | Lean | — | ⏳ open, deepest (~80-150 LOC) |
| S5 ACT (TendstoUniformlyOn on compacta) | Lean | — | ⏳ open, ~30 LOC (uses S4a + `tendstoUniformlyOn_tsum_nat`) |
| S6 ACT (DCT interchange + axiom discharge) | Lean | — | ⏳ deep, depends on S3 + S4c + S5 |

## Attempt Count
- Total attempts: 4
- Current approach attempts: 3
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

**Post-S4a priority order:**

1. **S4b — Uniform summability on compact subsets.** Given S4a, the
   M-test gives `Summable (fun n => R^n)` (for `R < 1`) as a dominating
   series independent of `x`. Use `Summable.of_nonneg_of_le` with the
   uniform bound from S4a to produce a `Summable` proof valid for all
   `x` with `|x| ≤ R`, then wrap as `TendstoUniformlyOn`. ~20 LOC,
   straightforward.

2. **S4c — Binomial series identity.** Mathematical core:
   `(1 - u)^(-1/2) = ∑ centralBinom n / 4^n · u^n` for `|u| < 1`. Likely
   ~80-150 LOC. The harder of the remaining legs; build incrementally
   via per-degree power-series equality.

3. **S5 ACT — Uniform-on-compacta `TendstoUniformlyOn`.** Promotes S4b
   from pointwise summability to uniform-on-compacta convergence of
   partial sums. Use Mathlib's `tendstoUniformlyOn_tsum_nat` or
   `Summable.tendstoUniformlyOn_partialSum`. ~30 LOC.

4. **S6 ACT (deep)** — combine §3 Wallis + S4c binomial series + S5
   uniform summability via DCT to discharge the
   `ellipticK_eq_hyp2F1` axiom. Multi-hundred LOC, deferred.

**Recommendation**: S4b next (mechanical / M-test), then S4c (genuine
analysis work), then S5, then S6.

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
- **S4a ACT** (2026-06-09, researcher-1, this session): Lean +15 LOC —
  `hypCoeff_mul_pow_abs_le_of_abs_le`. `x`-independent M-test
  primitive on compact subsets of `(-1, 1)`. See
  `sessions/2026-06-09-s04a-act-mtest-primitive.md`.
