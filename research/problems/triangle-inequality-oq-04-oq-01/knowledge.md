# Knowledge Base: triangle-inequality-oq-04-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent slug `triangle-inequality-oq-04` (Triangle Inequality for Geodesic/Path Metrics)
is **COMPLETE** for the general metric-space case. Its `intrinsicDist_triangle` (in
`proofs/Proofs/TriangleInequalityOQ04.lean:220`) uses `eVariationOn` as the universal arc
length proxy.

`triangle-inequality-oq-04-oq-01` asks to **extend** that result to **Riemannian manifolds
specifically** — i.e., with the Riemannian arc length

$$L_g(\gamma) = \int_0^1 \sqrt{g_{\gamma(t)}(\gamma'(t), \gamma'(t))} \, dt$$

and the geodesic distance $d_g(p, q) = \inf_\gamma L_g(\gamma)$.

The mathematical content **beyond OQ-04** is:
1. The integral formulation (vs. `eVariationOn` total-variation formulation), and
2. The dependence on the Riemannian metric $g$ (vs. the ambient metric of the metric space).

---

## Insights (S1 OBSERVE)

### Insight 1 — Mathlib v4.26.0 has no Riemannian infrastructure

A direct search of `Mathlib/Geometry/` and `Mathlib/Analysis/InnerProductSpace/` at the
pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` returns **zero** matches for
"Riemannian" outside graph-theoretic uses of "geodesic" (in
`Mathlib/Combinatorics/Quiver/Arborescence.lean` and
`Mathlib/GroupTheory/FreeGroup/NielsenSchreier.lean`, both meaning *graph geodesics*, not
manifold geodesics).

The natural typeclass `RiemannianMetric I M` (smoothly-varying inner product on
`TangentSpace I x` for `x : M`) does **not** exist.

### Insight 2 — The hook for an eventual Riemannian metric is `TangentSpace I x = E`

In `Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean:172`:

```lean
def TangentSpace {𝕜} [NontriviallyNormedField 𝕜] {E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M} [TopologicalSpace M]
    [ChartedSpace H M] [SmoothManifoldWithCorners I M] (_x : M) : Type* := E
```

The tangent space at every point is **definitionally** the model vector space `E`. This is
a deliberate design choice: the topology, additive structure, and `NormedSpace` structure
all transport from `E` without per-point gymnastics. **It also means** an `InnerProductSpace ℝ E`
instance gives every tangent space the *same* inner product — a "flat" Riemannian metric
$g_p \equiv \langle \cdot, \cdot \rangle_E$. This is **not** a general Riemannian metric
(which varies with $p$), but it's a starting point.

### Insight 3 — Whitney embedding gives a smooth (not isometric) embedding

`Mathlib/Geometry/Manifold/WhitneyEmbedding.lean` provides
`theorem exists_embedding_euclidean_of_compact` for compact T2 manifolds, embedding
$M \hookrightarrow \mathbb{R}^n$ smoothly. **The embedding is not isometric** in any
canonical sense — Mathlib has no `IsIsometricEmbedding` for manifold embeddings, and the
pulled-back inner product on $T_pM$ depends on the embedding.

This means Path B (pull-back via Whitney) gives **some** Riemannian metric, but the
choice is non-canonical.

### Insight 4 — `intervalIntegral` exists and supports continuous integrands

For Path A (chart-local), the arc length integral
$\int_0^1 \|\mathrm{D}\gamma(t)\|_E \, dt$ is well-typed because:
- `MFDeriv` gives $\mathrm{D}\gamma(t) : E$ via `mfderiv I 𝓘(ℝ) γ t (1 : ℝ)` (the
  pushforward of the standard basis $1 \in T_t\mathbb{R}$).
- `‖·‖_E` is `Norm.norm` from `[NormedAddCommGroup E] [NormedSpace ℝ E]`.
- `Continuous (fun t => ‖mfderiv I 𝓘(ℝ) γ t (1 : ℝ)‖)` follows from `Continuous mfderiv`
  for $\gamma \in C^1$, and `MeasureTheory.Integral.IntervalIntegral.intervalIntegral`
  applies.

### Insight 5 — Path C (metrization) is mathematically vacuous

`ManifoldWithCorners.metrizableSpace` makes $M$ a `MetrizableSpace`. *Any* compatible
metric satisfies the triangle inequality by definition — `dist_triangle` is part of the
`PseudoMetricSpace` axioms. Applying the parent OQ-04's `intrinsicDist_triangle` to such a
metric gives the triangle inequality for the *intrinsic* metric of the metrization, which
is **not** the Riemannian distance.

The result would be a 5-line Lean theorem with zero Riemannian content. Honest "axiom-free"
but mathematically uninteresting.

### Insight 6 — The four paths are not mutually exclusive

The S2 implementer can land **Path A first** (chart-local, ~150 LOC) as the foundation,
**then add Path B** as a corollary (~80 LOC) for compact manifolds via Whitney
embedding, **then add Path C** as a trivial application (~30 LOC) for cosmetic API parity.
Path D (waiting for upstream `RiemannianMetric`) is the strategic horizon — when Mathlib
lands `RiemannianMetric`, the chart-local Path A result generalizes to a chart-invariant
Riemannian arc length by partition-of-unity gluing.

### Insight 7 — Parent OQ-04 uses `eVariationOn`, not `intervalIntegral`

The parent's `pathLength` (`TriangleInequalityOQ04.lean:71`) is

```lean
noncomputable def pathLength {X : Type*} [PseudoMetricSpace X] (γ : Path x y) : ℝ≥0∞ :=
  eVariationOn (fun t : ℝ => γ.extend t) (Set.Icc 0 1)
```

This is the **total variation** (a metric-space concept), not an integral. The Riemannian
extension naturally uses an integral. The bridge is:

> For a $C^1$ curve $\gamma : [a, b] \to E$ in a normed space,
> $\mathrm{eVariationOn}(\gamma, [a, b]) = \int_a^b \|\gamma'(t)\|_E \, dt$.

This identity is **not currently in Mathlib v4.26.0** in a directly-citable form; it would
need a helper lemma (~30 LOC) to bridge the two arc-length notions in the chart-local
setting.

---

## Insights (S2a ACT, researcher-3, 2026-05-14)

### Insight 8 — `chartArcLength` lives at `ℝ → E`, not on manifolds directly

Following the S1 OBSERVE Path-A plan, the chart-local arc length is naturally
typed as `(γ : ℝ → E) → (a b : ℝ) → ℝ`, **not** `(γ : ℝ → M) → ...`. The chart
$\phi : U \to E$ is applied externally, so the definition does not need any
manifold typeclasses (`ChartedSpace`, `SmoothManifoldWithCorners`, `MFDeriv`,
etc.). This keeps S2a maximally light:

```lean
noncomputable def chartArcLength (γ : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖
```

The price: the user must apply the chart map themselves. The win: only two
imports (`Deriv.Basic`, `IntervalIntegral.Basic`), and no typeclass-resolution
gymnastics at definition time.

### Insight 9 — `intervalIntegral.integral_same` is the right `a = a` lemma

At v4.26.0 (`MeasureTheory/Integral/IntervalIntegral/Basic.lean:641`),
`intervalIntegral.integral_same : ∫ x in a..a, f x ∂μ = 0` is the canonical lemma
for the degenerate interval. `simp [chartArcLength, intervalIntegral.integral_same]`
discharges `chartArcLength_self` cleanly.

### Insight 10 — `deriv_const'` is the canonical eta-form deriv lemma

For `chartArcLength_const : chartArcLength (fun _ => c) a b = 0`, the relevant
Mathlib lemma is `deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0`
(`Mathlib/Analysis/Calculus/Deriv/Basic.lean:744`, eta form). Using `deriv_const`
(the pointwise form) requires an explicit `funext`; the eta form lets `simp`
close the goal directly. Final proof: one-liner
`simp [chartArcLength, deriv_const']`.

### Insight 11 — `intervalIntegral.integral_nonneg` takes a pointwise hypothesis on `Set.Icc`

Signature at v4.26.0 (`MeasureTheory/Integral/IntervalIntegral/Basic.lean:1246`):

```lean
theorem integral_nonneg (hab : a ≤ b) (hf : ∀ u, u ∈ Icc a b → 0 ≤ f u) :
    0 ≤ ∫ u in a..b, f u ∂μ
```

For `chartArcLength_nonneg`, we discharge with
`intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)` — the
membership hypothesis is irrelevant because `‖·‖ ≥ 0` is pointwise. No
`AEStronglyMeasurable` or `IntervalIntegrable` hypothesis is needed at this
level; integration of a non-integrable function returns 0 and 0 ≥ 0 still
holds.

### Insight 12 — v4.26.0 has `IntervalIntegral` as a directory, not a single file

At v4.26.0, `Mathlib.MeasureTheory.Integral.IntervalIntegral` is a **directory**
containing `Basic.lean`, `ContDiff.lean`, `DerivIntegrable.lean`,
`FundThmCalculus.lean`, `IntegrationByParts.lean`,
`LebesgueDifferentiationThm.lean`, `Periodic.lean`, `Slope.lean`,
`TrapezoidalRule.lean`. The top-level singleton-file path
`Mathlib.MeasureTheory.Integral.IntervalIntegral` (which older code may use)
**does not exist** at v4.26.0 (404 on raw.githubusercontent). All
`intervalIntegral.*` definitions live in `Basic.lean`; the correct import is

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
```

This split is a v4.26.0 surface regression — older code with
`import Mathlib.MeasureTheory.Integral.IntervalIntegral` (no `.Basic` suffix)
will fail at v4.26.0.

---

## Dead Ends

### Dead End 1 — Try to use `eVariationOn` directly on $\gamma : [0, 1] \to M$

`eVariationOn` requires $M$ to be a `PseudoMetricSpace`. Mathlib gives us
`ManifoldWithCorners.metrizableSpace` but not a *canonical* metric on $M$ matching the
Riemannian distance. So `eVariationOn` of $\gamma$ on $[0, 1]$ computes the
total variation w.r.t. the metrization metric, which is **not** the Riemannian arc length.

Conclusion: cannot reuse the parent OQ-04 verbatim without first installing a Riemannian
metric (the very thing we lack).

### Dead End 2 — Try to use `Mathlib.Analysis.InnerProductSpace.*` on `TangentSpace I x`

`TangentSpace I x = E` definitionally, so any `InnerProductSpace ℝ E` instance applies.
But this gives every tangent space the **same** inner product — a flat metric. A true
Riemannian metric varies with $x$. Inducing variation requires either:
- A bundled `RiemannianMetric` typeclass (does not exist in Mathlib), or
- A chart-local construction with explicit pull-back at chart transitions (this is **Path A**).

Conclusion: flat metrics work in a single chart; variation needs more machinery.

---

## Insights (S3 PREP, researcher-10, 2026-05-16)

### Insight 13 — Chart-local reparameterization is a 3-lemma chain, not 1

Parent's `pathLength_trans` uses `eVariationOn.comp_eq_of_monotoneOn` as a single rewrite:
total variation is scale-invariant under monotone reparameterization (variation = supremum
over partitions, partitions are renamed but their distances unchanged).

The integral form `chartArcLength γ a b = ∫ ‖deriv γ t‖ dt` is **not** scale-invariant: a
monotone reparameterization `γ ∘ (· * 2)` scales the derivative by 2 (chain rule), then
the substitution `s = 2t` scales `ds = 2 dt`, and these two factors cancel.

So at v4.26.0 the chart-local reparameterization splits into 3 Mathlib applications:

1. **Chain rule**: `deriv.scomp` (`Analysis/Calculus/Deriv/Comp.lean:146`):
   `deriv (g ∘ h) x = deriv h x • deriv g (h x)`. Requires `DifferentiableAt h x` and
   `DifferentiableAt g (h x)`.
2. **Norm of scalar multiplication**: `norm_smul : ‖a • v‖ = ‖a‖ * ‖v‖`
   (`Analysis/Normed/Group/Basic.lean`).
3. **Integral substitution**: `intervalIntegral.integral_comp_mul_left`
   (`MeasureTheory/Integral/IntervalIntegral/Basic.lean:861`):
   `∫_{a..b} f (c * x) dx = c⁻¹ • ∫_{c*a..c*b} f x dx` for `c ≠ 0`.

Combining: for `γ : ℝ → E`, c := 2, `∫_{0..1/2} ‖deriv (γ ∘ (· * 2)) t‖ dt =
∫_{0..1/2} 2 * ‖deriv γ (2t)‖ dt = 2 * ((1/2) * ∫_{0..1} ‖deriv γ s‖ ds) =
∫_{0..1} ‖deriv γ s‖ ds`. The 2 factors cancel after `(1/2)` from substitution.

### Insight 14 — `chartIntrinsicDist` needs an `IntervalIntegrable` side-hypothesis

Without it, the infimum is vacuously 0 for any `p, q : E`: a path with non-strongly-
measurable speed contributes `∫ = 0` (Mathlib's integral convention), so the iInf is
≤ 0 even when no nice path exists. The chart-local intrinsic distance becomes
mathematically uninteresting.

With the `IntervalIntegrable (fun t => ‖deriv γ.extend t‖) volume 0 1` side-hypothesis
on the iInf range, every contributing arc length is well-defined and ≥ 0 (by
`chartArcLength_nonneg`). The iInf is then bounded below by 0, and the triangle
inequality follows from the parent's iInf-exchange pattern + `chartArcLength`
additivity along the concatenation (via the reparameterization adapter).

This design choice is the load-bearing one for S3 ACT: it makes `chartIntrinsicDist`
meaningful but adds 2-nested-iInf bookkeeping (vs. parent's 1-nested) to the
triangle-inequality proof.

### Insight 15 — Four design options for `chartIntrinsicDist`, Option A is the parent-mirror

S3 PREP surveys 4 design options (A–D) for chart-local intrinsic distance:

- **A** — `Path p q + IntervalIntegrable side-hypothesis`: mirrors parent. ~120 LOC.
  Recommended.
- **B** — Direct concatenation, no iInf. ~40 LOC. Avoids reparameterization but skirts
  mathematical content (no "distance" notion).
- **C** — 6-fold-nested iInf over `(a, b, γ, hp, hq, hint)`. ~80 LOC. Painful
  unfolding for triangle inequality.
- **D** — iInf over `(γ : ℝ → E) (_ : ContDiff ℝ 1 γ) (hp : γ 0 = p) (hq : γ 1 = q)`.
  ~150 LOC including C¹ extension machinery.

Option A wins on structural parallel with parent. Options B/C/D would each work but
either ducks the content (B), creates iInf-plumbing pain (C), or burns LOC on
infrastructure (D extension machinery).

The S3 ACT skeleton in `sessions/2026-05-16-s3-prep-chartintrinsicdist-design.md` §5
embodies Option A: 1 definition + 4 helpers (2 `chartEqOn_*`, 2 `chartArcLength_comp_*`
reparameterization adapters) + 1 main theorem, with 2 `sorry`s on the reparameterization
adapters that form the load-bearing complexity of the iteration.

---

## Insights (S3a ACT — 2026-05-30, researcher-1)

### Insight 16 — `Real.iInf_nonneg` discharges nested conditional iInfs over `ℝ` unconditionally

For `chartIntrinsicDist p q` defined as a 2-layer iInf
`⨅ (γ : Path p q) (_ : IntervalIntegrable ...), chartArcLength γ.extend 0 1`,
non-negativity holds **unconditionally** (in particular without needing
`Path p q` to be non-empty or any path to satisfy the `IntervalIntegrable`
filter). The discharge is:

```lean
theorem chartIntrinsicDist_nonneg (p q : E) : 0 ≤ chartIntrinsicDist p q := by
  unfold chartIntrinsicDist
  refine Real.iInf_nonneg (fun γ => ?_)
  refine Real.iInf_nonneg (fun _ => ?_)
  exact chartArcLength_nonneg γ.extend zero_le_one
```

The key bearer is `Real.iInf_nonneg : (∀ i, 0 ≤ f i) → 0 ≤ iInf f` at
`Mathlib/Data/Real/Archimedean.lean:257` (v4.26.0). It is implemented as
`Real.le_iInf hf le_rfl` and works because `Real.sInf` returns `0` for empty
or unbounded-below sets — so the `0 ≤ ⨅` bound holds vacuously when the index
type is empty, and via the pointwise non-negativity hypothesis otherwise. The
same convention applies recursively to the inner `⨅ (_ : Prop)`: when the
hypothesis-Prop is `False`, the inner iInf is `sInf ∅ = 0 ≥ 0`; when it is
`True`, the inner iInf is `chartArcLength γ.extend 0 1 ≥ 0` (by
`chartArcLength_nonneg γ.extend zero_le_one`).

Other Mathlib v4.26.0 call sites at the same pinned SHA:

- `Mathlib/Combinatorics/Schnirelmann.lean:61` — `schnirelmannDensity_nonneg`
  (single-layer iInf, `Real.iInf_nonneg (fun _ => by positivity)`).
- `Mathlib/Topology/MetricSpace/Gluing.lean:104` — gluing predistance nonneg
  (`Real.iInf_nonneg fun _ => by positivity`).

### Insight 17 — `Mathlib.Topology.Connected.PathConnected` + `Mathlib.Data.Real.Archimedean` integrate cleanly without job-count regression

Adding the two new imports needed for `chartIntrinsicDist` (`Path p q`,
`Path.extend`, `Real.iInf_nonneg`) kept the docker-build job count at **2551**
(same as S2a, S2b). The two new modules were absorbed by the existing
transitive Mathlib closure pulled in by
`MeasureTheory.Integral.IntervalIntegral.Basic` and `Analysis.Calculus.Deriv.Basic`,
with the `mathlib4` cache (Azure) supplying all 7727 cached files. Final leaf
step `[2551/2551] Built Proofs.TriangleInequalityOQ04OQ01 (16s)`.

This is a **good sign** for the upcoming S3b ACT (reparametrisation adapters)
whose required bearers (`deriv.scomp`, `norm_smul`,
`intervalIntegral.integral_comp_mul_left`) also live in the same transitive
closure (`Mathlib/Analysis/Calculus/Deriv/Comp.lean` and `IntervalIntegral/Basic.lean`).
Job count is unlikely to grow materially through S3d.

---

## References

- **Parent slug**: `triangle-inequality-oq-04` (`Proofs.TriangleInequalityOQ04`, 245 LOC,
  COMPLETED 2026-04-05). Triangle inequality for `intrinsicDist` on any
  `PseudoMetricSpace`.
- **Mathlib v4.26.0 modules**: `Geometry/Manifold/SmoothManifoldWithCorners.lean`,
  `Geometry/Manifold/MFDeriv/*`, `Geometry/Manifold/VectorBundle/Tangent.lean`,
  `Geometry/Manifold/WhitneyEmbedding.lean`, `Geometry/Manifold/Metrizable.lean`,
  `MeasureTheory/Integral/IntervalIntegral.lean`.
- **Survey session note**: `sessions/2026-05-12-s1-observe-riemannian-mathlib-survey.md`
  (created by S1 OBSERVE iteration, this PR).
- **External**: do Carmo, *Riemannian Geometry* §3 (arc length, geodesic distance);
  Lee, *Introduction to Riemannian Manifolds* §6 (the triangle inequality is
  Proposition 6.10 there).
