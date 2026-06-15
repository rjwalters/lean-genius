# Session 5 — Strategy D ACT: Lean transcription

**Date**: 2026-06-15
**Agent**: researcher-1
**Mode**: CONTINUE (ORIENT ACT-ready → ACT shipped, build-pending)
**Backends**: Docker `docker info` 20s timeout (DOWN); Aristotle MCP `prove` → "Resource not
found" (DOWN). Dual blackout — file ships build-pending, CI is ground truth.

## Decision

Strategy D had been "paste-port-ready" since S4 (researcher-5), with every integral-closure
bearer file:line-confirmed at Mathlib pin `v4.26.0` and the arithmetic durably verified by
`verify_strategy_d.py` (S3). Four sessions deferred the transcription waiting for a backend.
Re-confirming an already-stable verdict adds no information; the proportionate single-cycle move
when the slug is reclaimed is the transcription itself. So I wrote the Lean file.

## Artifact

`proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` — 5 theorems, 0 sorries,
0 axioms; registered in `proofs/Proofs.lean`.

Integral-closure descent for `α = √2+√3+√5+√7`:

1. `isIntegral_sqrt_natCast (k : ℕ) : IsIntegral ℤ (√(k:ℝ))` — witness `X²−C (k:ℤ)`, monic by
   `monic_X_pow_sub_C`, `aeval` reduction by `simp only [...]` then `Real.sq_sqrt`.
2. `alpha_isIntegral` — `(((h2.add h3).add h5).add h7)` with each `hk := simpa using
   isIntegral_sqrt_natCast k`.
3. `sqrt_bounds (x lo hi) (0≤lo) (0≤hi) (lo²<x) (x<hi²) : lo < √x ∧ √x < hi` — two `calc`s using
   `Real.sqrt_sq` and `Real.sqrt_lt_sqrt`; `0≤x` derived from `lo²<x`.
4. `alpha_gt_eight : 8 < α` and `alpha_lt_nine : α < 9` — instantiate `sqrt_bounds` at the
   witnesses (1.41/1.42, 1.73/1.74, 2.23/2.24, 2.64/2.65), then `linarith`.
5. `irrational_sqrt2_plus_sqrt3_plus_sqrt5_plus_sqrt7` — `rintro ⟨q,hq⟩`; descend via
   `isIntegral_algebraMap_iff (algebraMap ℚ ℝ).injective` (uses `eq_ratCast` to identify
   `algebraMap ℚ ℝ q` with `↑q`); `IsIntegrallyClosed.isIntegral_iff.mp` gives `q=(n:ℤ)`; then
   `8<(n:ℝ)<9` ⇒ `exact_mod_cast` + `omega`.

## Verification (build-free)

- `verify_strategy_d.py` re-run: ALL CHECKS PASSED — integrality of each √k, degree-16 minimal
  polynomial (resultant + `m(α)=0`), and the **exact** rational witnesses
  `141/100 < √2 < 71/50`, …, `66/25 < √7 < 53/20` that the Lean `norm_num` obligations encode.
- In-repo idiom confirmation: `monic_X_pow_sub_C` (NthRootIrrationalOQ01.lean:132,141),
  `isIntegral_algebraMap_iff (… ).injective` (AngleTrisectionOQ02OQ01OQ02Incomplete01.lean:171,414).

## Self-review fix

`sqrt_bounds` upper branch initially had `Real.sqrt_lt_sqrt (le_of_lt (by positivity)) h2`, but
`positivity` cannot establish `0 ≤ x` for an abstract `x`. Replaced with a derived
`hx : 0 ≤ x := le_of_lt (lt_of_le_of_lt (sq_nonneg lo) h1)`.

## Residual risk

Not Lean-checked (backends down). Two isolated plumbing risks if CI fails:
1. The `simp only` aeval lemma set in `isIntegral_sqrt_natCast`.
2. `IsIntegrallyClosed.isIntegral_iff` / `eq_ratCast` and the `IsScalarTower ℤ ℚ ℝ` /
   `IsFractionRing ℤ ℚ` instances firing without manual `haveI`.

The mathematics is verifier-confirmed; any failure is a one-line Lean fix, not a strategy change.

## Next

CI build. Green ⇒ OQ solved (0 sorries / 0 axioms), promote to completed. Red ⇒ patch the
flagged line per residual-risk notes.
