# S8 PREP — 9-day STATE-SYNC + tight Paley-Zygmund target refinement

**Date**: 2026-06-09
**Researcher**: researcher-11
**Iteration**: 10
**Type**: doc-only PREP (no `.lean` changes)

## §1 9-day STATE-SYNC snapshot

Since S6 ACT (PR #21601 / commit `a1ab1a83cdd`, merged 2026-05-31), the
file `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` has been **byte-stable**:

| Field | Value |
|------|------|
| Lines | 235 |
| Theorems (total / private) | 5 / 1 |
| Sorries | 0 |
| Axioms | 0 |
| Last commit | `a1ab1a83cdd` (2026-05-31) |
| Days since last commit | 9 |
| Open competing PRs on this file | 0 |
| Open competing PRs on companion JSON | 0 |

Verified via:
- `git log -1 -- proofs/Proofs/BirthdayProblemOQ01OQ02.lean`
- `wc -l` and `grep -cE` for theorem counts
- `gh pr list --state open` filtered on `birthday` (zero matches)

## §2 Mathlib pin bearer drift (26-day window)

| Field | Value |
|------|------|
| Lake SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| Input rev | `v4.26.0` |
| Days since `v4.26.0` freeze (2026-05-14) | 26 |
| Days since last bearer recheck (S7 PREP, 2026-05-30) | 10 |
| Net drift rows | 0 |

The five S6 ACT bearers — `Nat.cast_sub`, `field_simp`,
`Finset.prod_div_distrib`, `Finset.prod_const`,
`Nat.descFactorial_eq_prod_range` — carry forward. The four S4 ACT
bearers (`Real.add_one_le_exp`, `Real.exp_neg`,
`one_div_le_one_div_of_le`, plus `Complex.exp_neg` co-existence
note) likewise carry forward.

By the lake-manifest-byte-stability argument (S4c §3, S5 §2,
S6 STATE-SYNC §2), zero rows can have drifted since the manifest SHA
is identical to the one S6 ACT shipped against. No Docker re-verification
is owed.

## §3 Math check on the S5 target formula

State.md's "Next Action" (§"S5 PREP — Tight Paley-Zygmund") proposes:

```
E[X²] = E[X] + C(n,2)·(C(n,2) - 1) / d²
```

This iteration re-derives the formula from first principles to confirm it
is correct (and not a disjoint-pairs approximation):

Let `X = ∑_{1 ≤ i < j ≤ n} I_{ij}` where `I_{ij} := 𝟙[f(i) = f(j)]` and
`f : Fin n → Fin d` uniform. Then

```
E[X²] = ∑_{(i,j)} E[I_{ij}²] + 2 · ∑_{(i,j) < (i',j')} E[I_{ij} · I_{i'j'}]
```

For each unordered cross-pair `{(i,j), (i',j')}` with `(i,j) ≠ (i',j')`:

- **Case A** (disjoint, `|{i,j} ∩ {i',j'}| = 0`): four independent draws,
  `E[I_{ij} I_{i'j'}] = (1/d)² = 1/d²`.
- **Case B** (share one element, `|… ∩ …| = 1`): three draws constrained
  to a single value (e.g. `f(i) = f(j) = f(j')`), `P = 1/d²`.
- (Case `|… ∩ …| = 2` is excluded since we assume distinct unordered pairs.)

So `E[I_{ij} I_{i'j'}] = 1/d²` for **all** distinct unordered cross-pairs.
Then `Cov(I_{ij}, I_{i'j'}) = 1/d² − (1/d)·(1/d) = 0` for both cases. The
indicators are pairwise uncorrelated despite **not** being independent —
a clean fact about the birthday-problem indicator chain.

Hence

```
Var(X) = ∑ Var(I_{ij}) = C(n,2) · (1/d) · (1 − 1/d) = C(n,2) · (d−1) / d²
E[X²] = Var(X) + E[X]²
      = C(n,2)·(d−1)/d² + (C(n,2)/d)²
      = C(n,2)/d − C(n,2)/d² + C(n,2)²/d²
      = E[X] + C(n,2)·(C(n,2) − 1) / d²  ✓
```

So the state.md formula is **exact** (no approximation). Then

```
P-Z lower:  probCollision ≥ E[X]² / E[X²]
                          = m²/d² / (m/d + m(m−1)/d²)
                          = m² / (m·d + m(m−1))
                          = m / (d + m − 1)            (assuming m > 0)
                          = k(k−1)/2 / (d + k(k−1)/2 − 1)
                          = k(k−1) / (2d + k(k−1) − 2)
```

confirming the targeted tighter denominator `2d + k(k−1) − 2`.

**Numerical check**: at `n = 23, d = 365` (classic birthday threshold):

- Current S4 ACT lower bound: `23·22 / (2·365 + 23·22) = 506 / 1236 ≈ 0.40939`
- Targeted S5 ACT tighter lower bound: `506 / 1234 ≈ 0.41005`
- Gain Δ ≈ 0.00066 (slightly larger than the Δ ≈ 0.0003 estimate in
  state.md, which appears to have been an off-by-one in the original
  S5 PREP back-of-envelope — the gain is small either way).

## §4 Revised S5 ACT route — what we have vs what we need

The Paley-Zygmund identity `P(X > 0) ≥ E[X]² / E[X²]` is not stated as
such at the Mathlib v4.26.0 pin for **deterministic finite-sample-space**
random variables (only the abstract measure-theoretic version exists).

Two routes for S5 ACT remain on the table:

### Route Y-α — Combinatorial direct (no `Probability.Variance`)

Compute `E[X · I_{X ≥ 1}]² ≤ E[X²] · P(X ≥ 1)` from the finite-sum
Cauchy-Schwarz over `Fin n → Fin d`, then chain with the closed-form
`E[X²]` derived in §3. Stays entirely in Mathlib's `Finset.sum` /
`Cauchy-Schwarz.sum_mul_sq_le_sq_mul_sq` API.

**Pros**:
- No `Probability.Variance` dependency (the major MEDIUM-risk surface).
- Builds on existing OQ02 / OQ01OQ01 infrastructure.
- Each helper individually small (`E[X²]` closed form, Cauchy-Schwarz
  one-liner, algebraic simplification to `k(k−1) / (2d + k(k−1) − 2)`).

**Cons**:
- The bridge from `probCollision` (OQ02 product) to `P(X ≥ 1)` (OQ01OQ01
  counting) requires the S6 ACT `probAllDistinct_eq_descFactorial_div`
  bridge — but **that bridge is already shipped**, so this is unblocked.
- E[X²] expansion has both `i=i'` (diagonal) and `i≠i'` (cross) terms,
  each requiring a separate Finset bookkeeping step. Estimated 70–90 LOC.

### Route Y-β — `Mathlib.Probability.Variance` lift

Use `MeasureTheory.variance` / `MeasureTheory.evariance` family directly,
giving Paley-Zygmund via `ProbabilityTheory.measure_lt_inner_pos_pow_le_*`
(if it exists at the pin).

**Pros**: Shorter (~40 LOC if the named lemma exists).
**Cons**: API surface UNVERIFIED at v4.26.0 — the original MEDIUM-risk
flag from state.md applies. May require non-trivial measure-theoretic
plumbing (the uniform measure on `Fin n → Fin d` would need to be lifted
into `MeasureTheory.ProbabilityMeasure`, which is heavier than the
deterministic counting argument).

### Recommendation

**Route Y-α** preferred. The descFactorial bridge already shipped means
the OQ02-product ↔ OQ01OQ01-counting translation is solved upstream,
and the combinatorial Cauchy-Schwarz is a one-bearer-chain operation
(`inner_mul_le_norm_mul_norm` or its `Finset` variant).

S5 ACT therefore re-scopes from the original "120 LOC monolithic"
estimate to **70–90 LOC** (closer to the per-step costs of S2 / S3 / S4).

## §5 Suggested split for S5 PREP→ACT staging

To keep each PR small and Docker-verifiable, split the next non-PREP
iteration into three steps:

| Step | Output | LOC | Risk | Status |
|------|--------|----:|------|--------|
| S5a PREP | (this PR) doc-only — Y-α vs Y-β choice + math re-derivation | 0 | LOW | THIS ITER |
| S5b ACT  | Helper `expected_pairs_sq_eq` (closed-form `E[X²]`) | ~40 | LOW | next |
| S5c ACT  | Theorem `probCollision_ge_paley_zygmund_tight` chaining S5b + descFactorial bridge + Cauchy-Schwarz | ~40 | LOW-MED | next+1 |

S5b is independent of S5c and can be reviewed/landed first.

## §6 Risk register update

No new failure modes since S6 ACT. The F1–F9 + F-extra register from
S6 STATE-SYNC carries forward unchanged. For S5b/c ACT, two new
anticipated failure modes:

| Mode | Trap | Mitigation |
|------|------|------------|
| F10 | `Nat.choose` ↔ `(n·(n−1))/2` cast residue (the `Nat.choose_two_right` regression that already blocks the OQ01 import) | Stay in closed-form `k·(k−1)` arithmetic; do not import `BirthdayProblemOQ01` |
| F11 | Cauchy-Schwarz over `Finset`: the named bearer is `Finset.inner_mul_le_norm_mul_norm` (TBD at pin) vs `Finset.sum_mul_sq_le_sq_mul_sq` | S5b PREP doc-only iteration to confirm the bearer name |

## §7 Bearer-pin recheck table (compact)

| Bearer | Required for | Module | At pin? |
|------|------|------|------|
| `Nat.cast_sub` | descFactorial bridge | `Mathlib.Data.Nat.Cast.Basic` | ✓ (S6 ACT) |
| `Finset.prod_div_distrib` | descFactorial bridge | `Mathlib.Algebra.BigOperators` | ✓ (S6 ACT) |
| `Nat.descFactorial_eq_prod_range` | descFactorial bridge | `Mathlib.Combinatorics.Choose.Factorial` | ✓ (S6 ACT) |
| `Real.add_one_le_exp` | exponential bridge | `Mathlib.Analysis.SpecialFunctions.Exp` | ✓ (S4 ACT) |
| `Real.exp_neg` | exponential bridge | `Mathlib.Analysis.SpecialFunctions.Exp` | ✓ (S4 ACT) |
| `one_div_le_one_div_of_le` | exponential bridge | `Mathlib.Algebra.Order.Field.Basic` | ✓ (S4 ACT) |
| `Finset.sum_mul_sq_le_sq_mul_sq` | future S5c (Cauchy-Schwarz) | `Mathlib.Analysis.Inner.MulInequalities` | TBD (audit at S5b PREP) |

## §8 Bottom line

- **9 days of dormancy without drift.** File byte-stable, lake pin
  byte-stable, no open PR contention. The S6 ACT-era bracket
  `k(k−1) / (2d + k(k−1)) ≤ probCollision ≤ k(k−1) / (2d)` stands.
- **S5 target formula validated.** The E[X²] expansion is exact (not
  an approximation) because the birthday-problem indicators are
  pairwise uncorrelated. Numerical Δ ≈ 0.0007 (slightly larger than
  the original 0.0003 estimate).
- **Route Y-α (combinatorial direct) recommended over Y-β** (Mathlib
  Probability lift). Estimated LOC drops from 120 → 70–90 across two
  ACT PRs (S5b + S5c).
- **No Docker build owed.** This iteration is doc-only.

**Next Action**: S5b PREP — audit the named bearer for `Finset`-level
Cauchy-Schwarz at v4.26.0 (`Finset.sum_mul_sq_le_sq_mul_sq` vs
alternatives) and provide a paste-ready scaffold for the closed-form
`E[X²]` helper.
