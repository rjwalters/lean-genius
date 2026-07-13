# S1 OBSERVE — Riemannian Mathlib Survey

**Iteration**: S1 OBSERVE
**Author**: researcher-5
**Date**: 2026-05-12
**File**: this session note (no Lean changes; problem.md/state.md/knowledge.md created)

## Purpose

The parent slug `triangle-inequality-oq-04` (Triangle Inequality for Geodesic/Path
Metrics) is COMPLETED for the general metric-space intrinsic distance. The OQ-04-OQ-01
sub-question asks to **extend** this to **Riemannian manifolds**, i.e., to the geodesic
distance defined as the infimum of Riemannian arc lengths
$L_g(\gamma) = \int_0^1 \sqrt{g(\gamma'(t), \gamma'(t))} \, dt$.

This S1 OBSERVE iteration surveys **what Mathlib v4.26.0 actually provides** for
Riemannian-adjacent infrastructure, identifies the structural blocker (no
`RiemannianMetric` typeclass), and maps four intermediate paths (A, B, C, D) that the S2
implementer can take. The recommended S2 target is **Path A** (chart-local Euclidean
length, ~150 LOC).

## 1. Mathlib v4.26.0 status at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

### 1.a — What exists in `Mathlib/Geometry/Manifold/`

| File | Purpose | Relevance |
|------|---------|-----------|
| `SmoothManifoldWithCorners.lean` | Charted spaces, smooth manifolds with corners | **Foundational** |
| `ChartedSpace.lean` | Charts and atlases | **Foundational** |
| `VectorBundle/Tangent.lean` | `TangentSpace I x := E` definitionally | **Key hook** for future Riemannian metric |
| `MFDeriv/Defs.lean`, `Basic.lean`, etc. | Manifold derivatives, chain rule | **Needed for Path A** (`γ'(t)`) |
| `ContMDiff/Defs.lean`, `Basic.lean`, etc. | $C^k$ smoothness on manifolds | **Needed for Path A** (regularity of $\gamma$) |
| `IntegralCurve.lean` | Integral curves of vector fields | Related but not directly needed |
| `WhitneyEmbedding.lean` | $M \hookrightarrow \mathbb{R}^n$ for compact $M$ | **Key for Path B** |
| `Metrizable.lean` | `ManifoldWithCorners.metrizableSpace` | **Key for Path C** |
| `PartitionOfUnity.lean` | Partitions of unity on manifolds | **Needed for chart-glue** (eventual Riemannian extension) |
| `Algebra/LieGroup.lean`, `LeftInvariantDerivation.lean` | Lie groups | Unrelated to OQ-01 |
| `Diffeomorph.lean`, `LocalDiffeomorph.lean` | Diffeomorphisms | Unrelated to OQ-01 |
| `PoincareConjecture.lean` | Statement of the Poincaré conjecture | Unrelated; named after but separate |
| `Complex.lean`, `AnalyticManifold.lean`, `ConformalGroupoid.lean` | Complex-analytic manifolds | Unrelated to OQ-01 |

### 1.b — What does NOT exist (confirmed by `grep -r "Riemannian"` over Mathlib at pinned rev)

Outside graph-theoretic uses of "geodesic" (3 hits in
`Mathlib/Combinatorics/Quiver/Arborescence.lean`,
`Mathlib/GroupTheory/FreeGroup/NielsenSchreier.lean`,
`Mathlib/Data/List/EditDistance/Defs.lean` — all meaning *graph distance*, not manifold
geodesic), **zero** files in Mathlib match "Riemannian". The following are absent:

- `class RiemannianMetric` — smoothly-varying inner product on `TangentSpace I x`.
- `def arcLength_g` — Riemannian arc length integral.
- `def geodesic` — locally length-minimizing curve, or the ODE solution.
- `def geodesicDist` — infimum of Riemannian arc lengths.
- `theorem geodesicDist_triangle` — the actual OQ-01 statement.
- `theorem hopf_rinow` (geodesic completeness ↔ metric completeness for Riemannian manifolds).
- `def CovariantDerivative`, `def LeviCivitaConnection`, `def CurvatureTensor`.

### 1.c — The structural blocker

The OQ-04-OQ-01 problem statement is mathematically meaningful **only** with a Riemannian
metric. Without `RiemannianMetric`, the integral $\int_0^1 \sqrt{g(\gamma'(t), \gamma'(t))} \, dt$
is not well-typed in Lean — there's no $g$ to plug in.

There is **no in-flight Mathlib PR** at the pinned rev for `RiemannianMetric`. Realistic
upstream timeline: not 2026 (full Riemannian framework is a multi-month contribution).

## 2. The four paths

### 2.a — Path A: chart-local Euclidean length

**Idea**: in a single chart $(U, \phi)$ of $M$ (with $\phi : U \to E$ a diffeomorphism to
an open subset of the model vector space $E$), a piecewise-smooth path $\gamma : [0, 1] \to U$
pushes forward to $\phi \circ \gamma : [0, 1] \to E$, which is a $C^1$ curve in a normed
space. Its arc length is

$$L(\phi \circ \gamma) = \int_0^1 \|(\phi \circ \gamma)'(t)\|_E \, dt.$$

This **chart-local arc length** is well-defined using only `MFDeriv` and `intervalIntegral`.
Define

$$d_{\phi}(p, q) := \inf \{ L(\phi \circ \gamma) \mid \gamma : [0,1] \to U, \gamma(0) = p, \gamma(1) = q \}$$

(the infimum over paths *staying in the chart*). The triangle inequality for $d_\phi$
follows by concatenation + additivity of `intervalIntegral`.

**Caveat**: $d_\phi$ depends on the chart $\phi$. A different chart gives a different
distance. **Not** the Riemannian distance, but a **chart-local approximation** that:

1. Is intrinsic to the chart (no embedding choice).
2. Reduces to the Euclidean distance in $E$ when $U$ is convex and $\phi$ is the identity.
3. Provides the **scaffolding** for a future Riemannian extension via partition of unity.

**LOC budget**: ~150 lines.

- ~25 lines: `chartArcLength` definition + `chartArcLength_const = 0` + sanity lemmas.
- ~35 lines: `chartArcLength_trans` (additivity under concatenation; mirrors
  `Proofs.TriangleInequalityOQ04.pathLength_trans`).
- ~30 lines: `chartIntrinsicDist` definition + nonneg + symmetric + identity-of-indiscernibles.
- ~40 lines: `chartIntrinsicDist_triangle` (the main theorem; mirrors
  `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle` proof structure).
- ~20 lines: docstrings + sphere/disk concrete instance (sanity check at the leaf).

**Mathlib API needed** (all present at v4.26.0):

| Symbol | Module | Purpose |
|--------|--------|---------|
| `MDifferentiable`, `mfderiv` | `Mathlib.Geometry.Manifold.MFDeriv.Defs` | $\gamma'(t)$ at a point |
| `ContMDiff`, `ContMDiff.of_succ` | `Mathlib.Geometry.Manifold.ContMDiff.Defs` | $C^k$ regularity |
| `intervalIntegral` | `Mathlib.MeasureTheory.Integral.IntervalIntegral` | $\int_0^1 \cdot \, dt$ |
| `intervalIntegral.integral_add_adjacent_intervals` | `Mathlib.MeasureTheory.Integral.IntervalIntegral` | $\int_0^{1/2} + \int_{1/2}^1 = \int_0^1$ |
| `Path.trans`, `Path.trans_extend` | `Mathlib.Topology.Connected.PathConnected` | Path concatenation |
| `Norm.norm`, `Continuous.norm` | `Mathlib.Analysis.Normed.Group.Basic` | $\|v\|_E$ |
| `ENNReal.iInf_add`, `add_iInf` | `Mathlib.Data.ENNReal.Basic` | Infimum-exchange (mirrors OQ-04) |

**Honest scope**: chart-local triangle inequality. Documented caveat that the result is
not chart-invariant. Aristotle-incompatible (the definition involves `intervalIntegral`
which is not in Aristotle's typeclass scope).

### 2.b — Path B: isometric embedding via Whitney

**Idea**: for compact T2 manifolds, Whitney's theorem
(`Mathlib.Geometry.Manifold.WhitneyEmbedding.exists_embedding_euclidean_of_compact`)
gives a smooth embedding $\iota : M \hookrightarrow \mathbb{R}^n$. Pull back the Euclidean
metric on $\mathbb{R}^n$ via $\iota$ to get a Riemannian metric on $M$. The arc length of
a path $\gamma$ in $M$ equals the arc length of $\iota \circ \gamma$ in $\mathbb{R}^n$.
The latter is already in `Mathlib.Analysis.BoundedVariation` via `eVariationOn`, and the
triangle inequality follows from the parent `Proofs.TriangleInequalityOQ04` applied to
$\mathbb{R}^n$.

**LOC budget**: ~80 lines (reducing to OQ-04).

**Caveat**: the result depends on the choice of Whitney embedding. Different embeddings
give different Riemannian metrics. The triangle inequality holds for each, but the metric
itself is not intrinsic to $M$.

**Mathlib API needed**:

| Symbol | Module |
|--------|--------|
| `exists_embedding_euclidean_of_compact` | `Mathlib.Geometry.Manifold.WhitneyEmbedding` |
| `Path.map` (push forward path) | `Mathlib.Topology.Connected.PathConnected` |
| `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle` | in-tree |
| `eVariationOn.comp_eq_of_monotoneOn` etc. | inherited from OQ-04 |

**Honest scope**: applies to compact T2 manifolds only (Whitney's hypothesis). Path
metric is **extrinsic**, not the canonical Riemannian distance.

### 2.c — Path C: metrization

**Idea**: `ManifoldWithCorners.metrizableSpace` makes $M$ a `MetrizableSpace`. Choose any
compatible metric (Mathlib does this non-constructively). View $M$ as
`PseudoMetricSpace M` and apply `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle`
verbatim.

**LOC budget**: ~30 lines, mostly typeclass plumbing.

**Caveat**: the result is **mathematically vacuous**. The metric is non-canonical and has
no relation to a Riemannian metric (which we don't have). The "Riemannian extension" is
a Riemannian extension in name only.

**Recommendation**: Path C is not worth a standalone PR — better included as a
**Section** of the Path A or Path B PR demonstrating the contrast (chart-local vs.
extrinsic vs. metrization-trivial).

### 2.d — Path D: wait for upstream Mathlib

**Idea**: defer the Riemannian extension until Mathlib lands `RiemannianMetric`. When
that happens, the chart-local Path A result extends to a chart-invariant Riemannian arc
length via partition-of-unity gluing (using `Mathlib.Geometry.Manifold.PartitionOfUnity`
already in v4.26.0).

**Realistic timeline**: not 2026. Mathlib's Geometry/Manifold contributors are currently
focused on `ContMDiff`/`MFDeriv` API refinements; no public PR for `RiemannianMetric` at
the pinned rev.

**Action for OQ-01**: Path D is not actionable now, but it informs **how to structure
Path A**: write `chartArcLength` and `chartIntrinsicDist` in a way that generalizes
cleanly when the Riemannian metric drops, by taking `(arcLength_fun : Path p q → ℝ)` as
a parametric input.

## 3. Recommended S2 plan

**S2 ACT — Path A (chart-local Euclidean length)**, decomposed into 3 sub-iterations:

- **S2a (~50 LOC, easy)**: `chartArcLength` definition + `chartArcLength_refl = 0` +
  `chartArcLength_nonneg`. Single chart only. Apr-21 BinomialTheoremOQ04OQ02OQ01 pattern
  (one new file, ~50 lines, build verified).
- **S2b (~50 LOC, medium)**: `chartArcLength_trans` (additivity under `Path.trans`).
  Mirrors `Proofs.TriangleInequalityOQ04.pathLength_trans` with `intervalIntegral` in
  place of `eVariationOn`. The key API is
  `intervalIntegral.integral_add_adjacent_intervals` (split at $t = 1/2$).
- **S2c (~50 LOC, medium)**: `chartIntrinsicDist_triangle`. Mirrors
  `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle` proof structure: take infs over
  paths $\gamma_1 : p \to q$ and $\gamma_2 : q \to r$, apply `chartArcLength_trans` to
  $\gamma_1 \ast \gamma_2$, swap the infimum via `ENNReal.iInf_add` / `add_iInf`.

**S3 ACT — Path B (Whitney isometric embedding) as corollary**, ~80 LOC, compact $M$ only.
**S4 ACT — Path C documented as a Section**, ~30 LOC, included in Path A PR.
**S5+ — defer to Path D** when upstream `RiemannianMetric` lands.

After S2c, the file has `chartIntrinsicDist_triangle` (chart-local) with **0 sorries, 0
axioms** (modulo upstream Mathlib bugs). The slug status becomes
`status: axiomatized` (or `formalized` if any chart-glue placeholder is needed) — never
`verified` for the Riemannian claim, because the Riemannian metric is not formalized.

## 4. Confirmed dead ends

### 4.a — Try `eVariationOn` on $\gamma : [0, 1] \to M$ directly

`eVariationOn` requires `PseudoMetricSpace M`. Mathlib's `ManifoldWithCorners.metrizableSpace`
provides this **non-canonically**: any metrization gives a metric, but no canonical choice
links to a Riemannian structure. So `eVariationOn` measures total variation w.r.t. the
metrization metric, not the Riemannian arc length. The two are equal in special cases
(e.g. flat Euclidean structure) but not in general.

### 4.b — `InnerProductSpace ℝ E` on `TangentSpace I x = E` (flat metric)

This makes every tangent space have the **same** inner product — a flat Riemannian metric.
The geodesic distance is then the Euclidean distance pulled back by the chart, which
agrees with Path A. So this is **Path A in different language**, not a fifth path.

### 4.c — `Manifold.IntegralCurve` to define arc length

`IntegralCurve` is for integral curves of vector fields (autonomous ODEs). Arc length is
a different object — it's the integral of $\|\gamma'(t)\|$ over a *given* curve, not the
solution of an ODE. The two concepts coincide for geodesics (which are integral curves of
the geodesic spray on the tangent bundle), but the geodesic spray requires the
Levi-Civita connection — which requires a Riemannian metric.

## 5. Honest summary

The OQ-04-OQ-01 problem as literally stated **cannot be formalized at v4.26.0** because
the `RiemannianMetric` typeclass it references does not exist in Mathlib. The S1 OBSERVE
work concludes:

- **Path A** (chart-local Euclidean length) is the **correct S2 target**: ~150 LOC,
  proves a *chart-local* triangle inequality that serves as the structural foundation for
  a future Riemannian extension. **Honest scope**: not the Riemannian distance.
- **Path B** (Whitney embedding) is a complementary S3 corollary for compact manifolds.
- **Path C** (metrization) is a vacuous trivial corollary — not worth a standalone PR.
- **Path D** (wait for upstream) is the strategic horizon for the *literal* OQ-01 claim.

The S2 implementer should **write `chartArcLength` parametric in the norm**, so that when
upstream Mathlib lands `RiemannianMetric` (`norm := √g`), the chart-local result extends
to chart-invariant Riemannian arc length by partition-of-unity gluing without rewriting
the definitions.

## 6. Race / coordination notes

- This is iteration **S1** on a **fresh slug** (`knowledge_score=0`, EMPTY tier on
  claim). No prior PRs reference `triangle-inequality-oq-04-oq-01`. Pristine territory.
- Parent slug `triangle-inequality-oq-04` is COMPLETED (PR merged 2026-04-05); no risk of
  parent drift.
- Sibling slugs `triangle-inequality-oq-02`, `triangle-inequality-oq-03` have their own
  `.lean` files; OQ-01 will add `Proofs/TriangleInequalityOQ04OQ01.lean` as a new file
  (no in-place modification of existing proofs).
- Three sibling tier-B slugs were also fresh (0 open PRs + ≥14-day-old "merges"):
  `cevas-theorem-oq-04-oq-01`, `dissection-of-cubes-oq-04-oq-02`,
  `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02`. None overlap with
  `triangle-inequality-oq-04-oq-01`.

## 7. Outcome of this iteration

**Outcome**: progress (S1 OBSERVE complete, baseline survey + roadmap).
**Build status**: N/A (no Lean changes).
**Net change**:
- Filled `problem.md` (108-line stub template → ~135-line populated problem statement).
- Filled `state.md` (25-line stub → ~75-line S1 state).
- Filled `knowledge.md` (21-line stub → ~135-line knowledge log).
- Created `sessions/2026-05-12-s1-observe-riemannian-mathlib-survey.md` (this file).

**Next step**: S2 ACT Path A — write `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` with
`chartArcLength`, `chartArcLength_trans`, `chartIntrinsicDist`,
`chartIntrinsicDist_triangle`. Aim for ~150 LOC, 0 sorries (parametric in the norm, so it
extends cleanly when upstream lands `RiemannianMetric`).
