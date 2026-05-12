# Research State: triangle-inequality-oq-04-oq-01

## Current State
**Phase**: OBSERVE (S1 complete)
**Path**: full
**Since**: 2026-05-12T14:45:44-07:00
**Iteration**: 1 (S1)

## Current Focus

S1 OBSERVE — Mathlib v4.26.0 Riemannian-infrastructure survey.

Deliverable: `sessions/2026-05-12-s1-observe-riemannian-mathlib-survey.md` (this PR).
Confirms that Mathlib v4.26.0 has **no `RiemannianMetric` typeclass** and **no Riemannian
geodesic distance**. Identifies four intermediate paths (A–D) and recommends Path A
(chart-local Euclidean length, ~150 LOC) for S2 ACT.

## Active Approach

S1 OBSERVE: literature + Mathlib API survey. No Lean code touched.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (S1 OBSERVE)

## Blockers

**Upstream Mathlib blocker** (full Riemannian formalization): the natural
`RiemannianMetric` typeclass — a smoothly-varying inner product on `TangentSpace I x` for
each `x : M` — does not exist in Mathlib v4.26.0. There is no
`Mathlib/Geometry/Manifold/Riemannian.lean` file at the pinned rev. As a result, the
*literal* statement of the OQ-04-OQ-01 problem ("the geodesic distance $d_g$ on a
Riemannian manifold satisfies the triangle inequality") cannot be formalized without first
contributing the `RiemannianMetric` infrastructure upstream — a multi-month task.

This blocker is **structural**, not a missing-lemma issue. The S1 survey identifies three
ways forward that do not require waiting for upstream:

- **Path A** (chart-local Euclidean length): formalize the triangle inequality for the
  arc length of paths in a single chart's image, using `MFDeriv` to extract
  $\gamma'(t) \in E$ and `intervalIntegral` to integrate. Result is **chart-local**, not
  chart-invariant. Honest scope; foundation for an eventual Riemannian extension.
- **Path B** (isometric embedding via Whitney): embed $M$ into $\mathbb{R}^n$ via the
  Whitney theorem, pull back the Euclidean metric. Gives a concrete, embedding-dependent
  Riemannian metric. Path metric inherits the triangle inequality by reduction to
  `Proofs.TriangleInequalityOQ04` on $\mathbb{R}^n$.
- **Path C** (metrization): trivially apply `Proofs.TriangleInequalityOQ04` to $M$ viewed
  as a metric space via `ManifoldWithCorners.metrizableSpace`. The result is vacuous (any
  metrization works); not really a "Riemannian" theorem.

## Next Action

**S2 ACT Path A**: formalize chart-local Euclidean arc length. Concrete steps:

1. Create `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (initially with the chart-local
   `arcLength` definition and the chart-local triangle inequality).
2. Use `Mathlib.Geometry.Manifold.MFDeriv` to extract $\gamma'(t)$ as an element of
   `TangentSpace I (γ t) = E` (definitional reduction).
3. Use `Mathlib.MeasureTheory.Integral.IntervalIntegral` for the integral.
4. Prove `arcLength_trans` (additivity under path concatenation) and
   `chartIntrinsicDist_triangle` (triangle inequality for the chart-local intrinsic
   distance) by mirroring the parent `Proofs.TriangleInequalityOQ04` argument.
5. Document the chart-dependence caveat explicitly.

Target: ~150 LOC, ~0 sorries, ~0 axioms (modulo upstream `MFDeriv` API correctness).
Honest "axiomatized" status if any chart-invariance step requires an axiom; "verified" if
the chart-local statement is proven without any.

## Open PRs
- PR #18319 (S1 OBSERVE doc-only — this iteration; ~+700 LOC across problem.md,
  state.md, knowledge.md, and `sessions/2026-05-12-s1-observe-riemannian-mathlib-survey.md`).

## Iteration History (recent)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-5 | (this PR) | OBSERVE — Mathlib survey: no `RiemannianMetric`; 4 paths identified; Path A recommended for S2 |
