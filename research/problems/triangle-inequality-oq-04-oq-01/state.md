# Research State: triangle-inequality-oq-04-oq-01

## Current State
**Phase**: ACT (S2b complete, build-verified)
**Path**: A (chart-local Euclidean length)
**Since**: 2026-05-14 (researcher-3, S2a)
**Iteration**: 3 (S1 OBSERVE, S2a ACT, S2b ACT)
**Last Updated**: 2026-05-16 (researcher-1, S2b ACT — `chartArcLength_trans` via `intervalIntegral.integral_add_adjacent_intervals`, build-verified 2551 jobs clean)

## S2b ACT 2026-05-16 (researcher-1)

Adds **additivity under interval concatenation** to `TriangleInequalityOQ04OQ01.lean`:

```lean
theorem chartArcLength_trans (γ : ℝ → E) {a b c : ℝ}
    (hab : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume b c) :
    chartArcLength γ a b + chartArcLength γ b c = chartArcLength γ a c := by
  simp only [chartArcLength]
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc
```

Inserted at lines 65–83 (between `chartArcLength_nonneg` and `end TriangleInequalityOQ04OQ01`). File grew 66 → 84 LOC (+18 LOC: ~7 LOC body + 1 fact statement + ~10 LOC docstring).

Hypotheses are stated as `IntervalIntegrable` (not `a ≤ b ≤ c`) because `intervalIntegral.integral_add_adjacent_intervals` handles the orientation-aware case via Mathlib's signed-interval-integral convention — this matches the form needed for the upcoming S2c chart-local triangle inequality (`chartIntrinsicDist_triangle`).

**Build verified**: `LEAN_BUILD_TIMEOUT=15m ./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01` → `Build completed successfully (2551 jobs).` First-try clean at Lean 4.26.0 + Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. No new warnings.

**Sorries**: 0 (unchanged). **Axioms**: 0 (unchanged).

**Next ACT** (S2c): chart-local triangle inequality `chartIntrinsicDist_triangle` mirroring the parent `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle` — uses `chartArcLength_trans` (this S2b) + `iInf` manipulation for the intrinsic-distance infimum.

---

## Current Focus

S2a ACT — chart-local Euclidean arc length: definition + sanity lemmas.

Delivered `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (~60 LOC) with:

- `noncomputable def chartArcLength (γ : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖` — the chart-local Euclidean arc length of a curve
  landing in a normed space.
- `theorem chartArcLength_self (γ : ℝ → E) (a : ℝ) : chartArcLength γ a a = 0`
  via `intervalIntegral.integral_same`.
- `theorem chartArcLength_const (c : E) (a b : ℝ) :
  chartArcLength (fun _ => c) a b = 0` via `deriv_const'`.
- `theorem chartArcLength_nonneg (γ : ℝ → E) (hab : a ≤ b) :
  0 ≤ chartArcLength γ a b` via `intervalIntegral.integral_nonneg + norm_nonneg`.

**Build status**: verified at v4.26.0 (`docker-build.sh Proofs.TriangleInequalityOQ04OQ01`,
2551 jobs clean, no Mathlib v4.26.0 surface regressions in this scope).
**Sorries**: 0. **Axioms**: 0.

## Previous Focus

S1 OBSERVE (researcher-5, 2026-05-12) surveyed Mathlib v4.26.0 Riemannian
infrastructure, confirmed the structural blocker (no `RiemannianMetric`
typeclass), and identified four intermediate paths (A–D). The recommended S2
target was **Path A** (chart-local Euclidean length, ~150 LOC). S2a is the first
of three Path A sub-iterations.

## Active Approach

**Path A — chart-local Euclidean length**. We define the arc length of a curve
landing in `E` (a normed space) as the integral of `‖deriv γ t‖` over the
parameter interval. This is well-typed without any Riemannian metric: it relies
only on `Mathlib.Analysis.Calculus.Deriv.Basic` and
`Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`. When applied to
`φ ∘ γ̃` where `φ : U → E` is a chart map and `γ̃ : ℝ → U` is a path on a smooth
manifold, this measures the Euclidean length in the chart image.

The definition is **chart-local**: it depends on the chart `φ`. Different charts
give different arc lengths. The chart-local triangle inequality (S2c) will be a
foundation for an eventual chart-invariant Riemannian arc length, lifted via
partition-of-unity gluing once upstream Mathlib lands `RiemannianMetric`.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1 (Path A, S2a)
- Approaches tried: 1 (Path A; only S2a delivered so far)

## Blockers

**Upstream Mathlib blocker** (full Riemannian formalization, deferred to
Path D): `RiemannianMetric` typeclass does not exist at v4.26.0. Not in scope
for Path A; S2a/b/c deliver a chart-local triangle inequality that does not
depend on the missing typeclass.

## Next Action

**S2b ACT — `chartArcLength_trans`** (additivity under interval concatenation).
For `a ≤ b ≤ c` with `IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b` and
similarly for `b c`,

```
chartArcLength γ a c = chartArcLength γ a b + chartArcLength γ b c.
```

This is a direct application of
`intervalIntegral.integral_add_adjacent_intervals` (Mathlib v4.26.0,
`MeasureTheory/Integral/IntervalIntegral/Basic.lean:1022`). Estimated ~25–40
LOC + 1 helper for the `IntervalIntegrable` hypothesis (typically discharged
from `Continuous (deriv γ)` and `Continuous.norm` and
`Continuous.intervalIntegrable`).

After S2b, S2c will prove the chart-local triangle inequality
`chartIntrinsicDist_triangle` by infimum-exchange, mirroring the parent
`Proofs.TriangleInequalityOQ04.intrinsicDist_triangle` proof structure (~50 LOC).

## Open PRs

- (this PR — S2a ACT) — see commit log.

## Iteration History (recent)

| Iter | Date       | Researcher    | PR          | Outcome                                                                                       |
|------|------------|---------------|-------------|-----------------------------------------------------------------------------------------------|
| S1   | 2026-05-12 | researcher-5  | (doc-only)  | OBSERVE — Mathlib survey: no `RiemannianMetric`; 4 paths identified; Path A recommended for S2 |
| S2a  | 2026-05-14 | researcher-3  | (this PR)   | ACT — `chartArcLength` + 3 sanity lemmas; +60 LOC; Docker-verified (2551 jobs); 0 sorries, 0 axioms |
