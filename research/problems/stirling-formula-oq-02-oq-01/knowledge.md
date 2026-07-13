# Knowledge: Continuous Stirling Formula for the Gamma Function

**Problem**: Prove the full continuous Stirling formula Γ(x+1) ~ √(2πx)·(x/e)^x for all real x > 0.

**Slug**: `stirling-formula-oq-02-oq-01` (child of `stirling-formula-oq-02`).

## Status: SOLVED (continuous form), 0 axioms, 0 sorries

Lean file: `proofs/Proofs/StirlingFormulaOQ02OQ01.lean`, namespace `StirlingGammaCont`.

Main results:
- `gamma_continuous_isEquivalent_stirling` : `(fun x => Γ(x+1)) ~[atTop] (fun x => √(2πx)·(x/e)^x)` — the headline `~` form.
- `log_gamma_continuous_stirling` : `log Γ(x+1) − (½·log(2πx) + x·log x − x) → 0` — the log form.

## Key insight (corrects the parent's assessment)

The parent entry `stirling-formula-oq-02` proved Stirling for Γ **only at integer
points** (via Γ(n+1)=n!) and stated the continuous version as an open question,
asserting it "requires the Laplace method (~500 lines of integral analysis not yet
in Mathlib)".

**This is overly pessimistic.** The continuous formula follows from two facts already
in Mathlib, with NO Laplace integral analysis:

1. `Stirling.factorial_isEquivalent_stirling` — the discrete formula n! ~ √(2πn)(n/e)^n.
2. `Real.convexOn_log_Gamma` — log-convexity of Γ on (0,∞).

This is the classical **Artin / Bohr–Mollerup** route.

## Proof architecture

Write n = ⌊x⌋. Log-convexity of Γ gives a two-sided **slope sandwich**:

    (x−n)·log n  ≤  log Γ(x+1) − log Γ(n+1)  ≤  (x−n)·log(n+1).

- Lower bound: `ConvexOn.slope_mono_adjacent` on the triple n < n+1 < x+1, using
  slope(n,n+1) = log Γ(n+1)/Γ(n) = log n.
- Upper bound: the chord/convex-combination inequality (`ConvexOn.2`) with
  x+1 = a(n+1)+b(n+2), a=(n+1)−x, b=x−n, using log Γ(n+2)/Γ(n+1) = log(n+1).

Combining with the discrete log-Stirling `log Γ(n+1) − logApprox n → 0` and the
algebraic identity (`error_identity`)

    (x−n)·log n + logApprox n − logApprox x
        = ½·log(n/x) + (x·log(n/x) + (x−n)),

the target log Γ(x+1) − logApprox x is squeezed between two functions both → 0.

## The crux estimate (`error_le_zero` / `error_ge`)

For x ≥ 1, n = ⌊x⌋:

    −1/n  ≤  x·log(n/x) + (x−n)  ≤  0.

- Upper: `log y ≤ y−1` (`Real.log_le_sub_one_of_pos`) at y=n/x gives
  x·log(n/x) ≤ x(n/x−1) = n−x, i.e. the bracket ≤ 0.
- Lower: same lemma at y=x/n gives log(n/x) ≥ 1−x/n, hence the bracket ≥
  −(x−n)²/n ≥ −1/n (since (x−n)² < 1).

Both bounds → 0: `½·log(n/x) → 0` (since ⌊x⌋/x → 1, `tendsto_nat_floor_div_atTop`),
the bracket → 0 by squeeze against ±1/⌊x⌋ → 0, and the upper-sandwich correction
(x−n)(log(n+1)−log n) → 0 (bounded by 1/⌊x⌋ via `log_le_sub_one_of_pos`).

## Mathlib lemmas that made it short
- `Real.convexOn_log_Gamma`, `ConvexOn.slope_mono_adjacent`, `ConvexOn.2` (chord).
- `Stirling.factorial_isEquivalent_stirling`, `isEquivalent_iff_tendsto_one`.
- `Real.log_le_sub_one_of_pos`, `tendsto_nat_floor_div_atTop`, `tendsto_nat_floor_atTop`.
- `Real.Gamma_add_one`, `Real.Gamma_pos_of_pos`, `Real.Gamma_nat_eq_factorial`.

## Verification
Type-checked with `lake env lean Proofs/StirlingFormulaOQ02OQ01.lean` (host Lean
4.26.0 against prebuilt Mathlib v4.26.0). Docker build wrapper was unavailable this
session; single-file host check used as the fallback. 0 sorries, 0 axioms,
`#print axioms` clean (only the foundational propext/Classical.choice/Quot.sound).

## Follow-up directions (not pursued)
- Ramanujan/Stirling series next term: log Γ(x+1) = … + 1/(12x) − … (needs error
  control beyond the leading log term).
- Bernoulli-number asymptotic expansion.
These are genuinely harder (real error estimates), distinct from this entry.
