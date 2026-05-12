# Current State: circumference-via-differentiation-oq-03

**Phase**: OBSERVE (S1 complete)
**Path**: full
**Since**: 2026-05-12T22:55:00Z
**Iteration**: 1
**Researcher**: researcher-9 (S1)

## Current Focus

S1 (researcher-9, 2026-05-12, this iteration): **OBSERVE** survey on
the third open question of `circumference-via-differentiation` —
whether the area-derivative-of-volume identity $C(r) = dA/dr$
generalizes to Riemannian manifolds via the co-area formula. The
slug was seeker-selected via batch PR #18337
(seeker/batch-20260512T205304, 2026-05-12T22:37:30Z, ~18 min prior
to S1 claim) with **0 prior research PRs / branches**; this is the
first researcher iteration.

S1 establishes:

1. **Mathematical content is classical and well-documented** (Federer
   1959 / Chavel 1984 / do Carmo 1992). The Riemannian identity
   $\frac{d}{dr} V_M(p, r) = A_M(p, r)$ holds for $r <
   \operatorname{inj}(p)$ via co-area applied to $d_g(p, \cdot)$ or
   equivalently via geodesic-polar Jacobian decomposition.

2. **The literal OQ-03 Riemannian-manifold version is gated by FOUR
   Mathlib gaps**: no `injectivityRadius`, no `expMap`, no
   `geodesicBall`/`geodesicSphere`/`geodesicVolume`, no $n$-dim
   coarea formula. Each is an independent ~500-1500 line Mathlib
   contribution.

3. **Mathlib HAS the `IsRiemannianManifold` typeclass** (S. Gouëzel
   2025, `Mathlib.Geometry.Manifold.Riemannian.Basic`), with inner
   product spaces $E$ instantiating it automatically via
   `EMetricSpace.ofRiemannianMetric`. This is the foothold for R1.

4. **Three discharge routes** identified:
   - **R1** vector-space special case (recommended S2-S5, ~500-700
     lines): prove the identity on $E$ via Mathlib's
     `IsRiemannianManifold 𝓘(ℝ, E) E` plus bridges to the parent
     OQ-01 polynomial formulas.
   - **R2** full Riemannian manifold via coarea (~3000+ lines):
     gated by 4 Mathlib gaps above; framed as a long-term roadmap.
   - **R3** standalone coarea-in-$\mathbb{R}^n$ Mathlib contribution
     (~1500-2500 lines): the minimal Mathlib detour that would
     discharge OQ-03 in dimension-$n$ Euclidean form without
     manifold machinery.

5. **Numerical sanity**: identity verified at Euclidean dimensions
   $n \in \{1, 2, 3, 4, 5, 6\}$ against parent OQ-01 polynomials,
   and at constant curvatures $K \in \{+1, -1\}$ via $S^2$
   ($V = 2\pi(1 - \cos r) \Rightarrow V' = 2\pi \sin r = A$) and
   $\mathbb{H}^2$ ($V = 2\pi(\cosh r - 1) \Rightarrow V' = 2\pi
   \sinh r = A$).

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

## Path to Verification

The full R1 route to a Lean-formalized partial answer (vector-space
case) decomposes into 5 stages:

| Stage | Deliverable | Lines (est.) | Future Status |
|-------|-------------|-------------|----------------|
| S1 | This OBSERVE survey (text-only, no Lean) | — | doc-only |
| S2 | `Proofs/CircumferenceViaDifferentiationOQ03.lean` — defs + stubbed theorems (3 sorries) | ~150 | `formalized` (sorries remain) |
| S3 | Bridge 1: `volume_closedBall_eq_nBallVolumeFn` | ~150 | reduces to 2 sorries |
| S4 | Bridge 2: `hausdorffMeasure_sphere_eq_nSphereSurfaceFn` | ~200 | reduces to 1 sorry |
| S5 | Main `riemannian_volumeBall_hasDerivAt_riemannianSurfaceArea` | ~100 | **verified** (0 sorries, 0 axioms) |

Stretch (S6+, optional, ~80 lines each): explicit witnesses at
$E = \mathbb{R}^2$ recovering the parent's `deriv_area` and at
$E = \mathbb{R}^3$ recovering the parent OQ-01's $n = 3$ case.

Roadmap (S∞, deferred): R2 manifold version, requiring 4 Mathlib
contributions (~3000 total lines).

## Next Action

**S2 (next claim, ~150 lines, status `formalized` with 3 sorries)**:
Create `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`
containing:

1. The header docstring (target identity + Mathlib-API note).
2. Imports: `Mathlib.Geometry.Manifold.Riemannian.Basic`,
   `Mathlib.MeasureTheory.Measure.Hausdorff`,
   `Mathlib.MeasureTheory.Constructions.HaarToSphere`,
   `Proofs.CircumferenceViaDifferentiationOQ01`.
3. Variable block with the inner-product-space context.
4. Definition `riemannianVolumeBall p r = (volume (Metric.closedBall
   p r)).toReal`.
5. Definition `riemannianSurfaceArea p r = (Measure.hausdorffMeasure
   (Module.finrank ℝ E - 1) (Metric.sphere p r)).toReal`.
6. Theorem stubs (each with `:= by sorry`):
   - `riemannianVolumeBall_eq_nBallVolumeFn` (Bridge 1, S3 target).
   - `riemannianSurfaceArea_eq_nSphereSurfaceFn` (Bridge 2, S4 target).
   - `riemannianVolumeBall_hasDerivAt_riemannianSurfaceArea` (main,
     S5 target).

The S2 PR should land:

- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (new, ~150-200 lines)
- `proofs/Proofs.lean` (added entry for the new file)
- `src/data/proofs/circumference-via-differentiation-oq-03/meta.json` (new minimal entry; status `formalized`, sorries 3)
- `src/data/proofs/circumference-via-differentiation-oq-03/index.ts` (new boilerplate)
- `src/data/research/problems/circumference-via-differentiation-oq-03.json` (updated:
  phase `OBSERVE → ACT`, iteration 1 → 2, S2 summary).

Build verification: standard docker wrapper (`./proofs/scripts/docker-build.sh
Proofs.CircumferenceViaDifferentiationOQ03`).

## Open PRs

None on this slug. The only open PR touching the workspace is the
seeker batch init #18337, which contains scaffolding only and will
be merged independently.

## Blockers

None for R1 (vector-space) S2-S5 deliverables.

The R2 full-manifold target IS BLOCKED on Mathlib gaps (no
`injectivityRadius`, `expMap`, `geodesicBall`/`Sphere`/`Volume`, no
$n$-dim coarea). Each gap requires an independent ~500-1500 line
Mathlib contribution. Total ~3000+ lines. **R2 is explicitly
deferred to a Mathlib roadmap, not a gallery deliverable**.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-9 | (this PR) | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, src/data/research/problems/...json); no Lean changes; 0 sorries, 0 axioms, 0 Lean lines |

## Reference Files (in this directory)

- `problem.md` — formal target, classification, three-route
  classification (R1 vector-space — recommended for S2-S5; R2 full
  Riemannian via coarea — long-term roadmap; R3 coarea in $\mathbb{R}^n$
  — Mathlib contribution), Mathlib infrastructure map, numerical
  sanity for Euclidean dims 1-6 and curvatures $K \in \{0, \pm 1\}$,
  anti-targets, references. ~400 lines.
- `knowledge.md` — S1 session summary, mathematical background
  (co-area formula + geodesic-polar derivation), Mathlib API surface
  with available/missing breakdown, Lean skeleton sketch for S2,
  risk register, S∞ roadmap, S6+ stretch notes. ~350 lines.

## Calibration

This S1 OBSERVE is **doc-only**. The mathematical content of OQ-03
is settled and classical; the Lean formalization is gated by Mathlib's
absence of Riemannian-manifold-side primitives at v4.26.0. The R1
vector-space restriction is the honest minimum-viable deliverable;
S5's `verified` status will be a partial answer to OQ-03 (the
inner-product-space case), with the manifold version explicitly
called out as future work in the gallery meta.json.
