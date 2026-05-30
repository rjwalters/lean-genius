# Knowledge Base: euler-polyhedral-formula-oq-02-oq-01-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Target: prove the full smooth Gauss-Bonnet theorem with boundary
```
∫_M K dA + ∫_∂M κ_g ds = 2π · χ(M)
```
for compact Riemannian 2-manifolds, **from first-principles Mathlib infrastructure** (no axiomatized fields encoding the result).

The parent file `proofs/Proofs/EulerPolyhedralOQ02OQ01.lean` axiomatizes Gauss-Bonnet as a structure field (`CompactRiemannianSurface.gauss_bonnet : totalCurvature = 2 * π * chi`) and derives algebraic consequences (genus formulas, sphere/torus/hyperbolic specializations). That is a *model*, not a proof; the field is a structure-encoded assumption, so the result is `axiomatized` rather than `verified` regardless of having 0 `axiom` declarations.

---

## Mathlib Infrastructure Survey (2026-05-30)

The proofs project pins Mathlib **v4.26.0** (`proofs/lakefile.toml`). Mathlib `master` has progressed; the gap analysis copied from the parent file's docstring is partially obsolete.

### What now exists upstream (Mathlib master, post-v4.26.0)

- `Mathlib/Geometry/Manifold/Riemannian/Basic.lean`
  - `IsRiemannianManifold` — Prop typeclass tying manifold distance to path-length integrals on tangent inner products.
  - `riemannianMetricVectorSpace` — the standard inner-product Riemannian metric on a vector space.
  - `PseudoEMetricSpace.ofRiemannianMetric`, `EMetricSpace.ofRiemannianMetric` — promote a Riemannian metric to an (extended) metric space.
- `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean`
  - `pathELength` (path length as `∫ ‖γ'‖`), `riemannianEDist` (infimum over C¹ paths), reparameterization invariance, triangle inequality.
- `Mathlib/Geometry/Manifold/VectorBundle/`
  - `Riemannian.lean` — Riemannian structure on a vector bundle.
  - `CovariantDerivative/Basic.lean`, `CovariantDerivative/Torsion.lean` — connections on bundles, torsion.
  - `LocalFrame.lean`, `Tensoriality.lean` — local frames and tensoriality lemmas (precursor APIs for curvature).

### What still does NOT exist upstream

- **No Gaussian curvature.** Search for `GaussianCurvature` returns nothing; no `K : RiemannianManifold → ℝ` is provided.
- **No geodesic curvature** of a curve in a Riemannian surface.
- **No Riemann curvature tensor.** A `CovariantDerivative` API is present but the tensor `R(X,Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_[X,Y] Z` is not exposed as a definition with the standard symmetries.
- **No manifold integration `∫_M ω` for differential forms,** no area form, no volume form derived from a Riemannian metric.
- **No de Rham complex / Stokes' theorem** at the differential-form level on manifolds with boundary. `Bordism.lean` exists but does not supply Stokes.
- **No Euler characteristic of a smooth manifold** defined intrinsically (triangulation, Morse, or de Rham).
- **No Gauss-Bonnet** theorem in any form.

### Status of Mathlib pin

Even the new Riemannian/CovariantDerivative material lands on `master` after the v4.26.0 tag. Bumping the local Mathlib pin is a prerequisite to *use* any of it; doing so is out of scope for a single research session because it can cascade into project-wide build effects.

---

## Insights

- The parent file's claim that "Mathlib (v4.26.0) does not yet have Riemannian metrics" is true at the pinned version but no longer literally true on master — Riemannian metric typeclasses and path-length API have landed. The remaining gap is the **curvature → integration → Stokes** stack, not the metric itself.
- A first-principles boundary-form Gauss-Bonnet proof requires, in roughly this order:
  1. Riemann curvature tensor on a smooth vector bundle with connection (CovariantDerivative is the right substrate).
  2. Gaussian curvature for a 2D Riemannian manifold derived from sectional curvature.
  3. Volume / area form `dA` from the Riemannian metric (oriented 2-form ω with ω(e1,e2)=1 on orthonormal frame).
  4. Geodesic curvature κ_g for a C² boundary curve.
  5. Manifold integration `∫_M K dA`, `∫_∂M κ_g ds` (Bochner integral against a measure, or differential-form integration with orientation).
  6. Stokes' theorem on manifolds with boundary, or an intrinsic Chern-style moving-frame proof.
  7. Euler characteristic of a smooth 2-manifold matching the topological one.
  8. Assemble Gauss-Bonnet via local Chern-style proof or via triangulation + discrete Gauss-Bonnet (already formalized for the polyhedral case in `EulerPolyhedralOQ02.lean`).
- Each step is comparable to a multi-month Mathlib contribution; assembled, this is on the order of several thousand lines of new infrastructure. Per the researcher rubric, this is **BLOCKED on missing Mathlib infrastructure > 1000 lines**.
- A productive *intermediate* milestone (still well beyond a single session) would be to formalize Gauss-Bonnet only for the **round 2-sphere `S²`** using Mathlib's existing stereographic charts (`Mathlib.Geometry.Manifold.Instances.Sphere`) plus an explicit integral computation `∫_{S²} 1 · dA = 4π = 2π · χ(S²) = 2π · 2`. That bypasses the curvature tensor entirely (`K ≡ 1`) and only needs an area-form definition on `S²` — still nontrivial, but the smallest meaningful concrete instance.

---

## Dead Ends

- **Axiomatizing the boundary Gauss-Bonnet equation as a structure field.** The parent file already does this for the closed case; replicating that for the boundary case adds no information beyond what the parent file would yield with a one-line extension. The research goal is explicitly "without assuming the Gauss-Bonnet equation as a field or axiom", so a structure-field approach defeats the purpose.
- **Submitting to Aristotle.** The blocking sorries here would be definition-level (curvature, area form, manifold integral) — Aristotle only proves theorem/lemma sorries with no definition sorries upstream of them.
- **Building from scratch in this repo.** Each piece is upstream infrastructure that belongs in Mathlib, not in a per-problem gallery file. Reimplementing it locally would create a parallel API that diverges from Mathlib's eventual choices.

---

## Current Status

**Phase**: SURVEY (advancing OBSERVE → SURVEY this session; no proof attempt warranted yet).
**Outcome**: BLOCKED on Mathlib infrastructure. Updated gap analysis: the Riemannian-metric layer has landed on Mathlib master; the curvature + manifold-integration + Stokes stack remains absent. Document the refined gap and the S²-only milestone as the smallest meaningful target.

## Next Steps

1. Watch Mathlib master for: (a) a Riemann curvature tensor on the tangent bundle via `CovariantDerivative`, (b) a manifold-volume / area-form construction from a Riemannian metric, (c) any `Stokes`/`integral_dω` API on manifolds with boundary. Any of those landing would change the assessment.
2. If/when the local Mathlib pin bumps past v4.26.0, port the parent file's structure-field model to optionally consume `IsRiemannianManifold` so the assumptions are at least stated against real Mathlib types rather than a bespoke structure.
3. Consider opening the **S² intermediate milestone** as its own subproblem (`euler-polyhedral-formula-oq-02-oq-01-oq-01-S2`) — first-principles Gauss-Bonnet for the round 2-sphere only, no boundary, constant curvature.
4. Until then, leave the parent file's axiomatized model untouched; do not add new structure-field "smooth-with-boundary" variants because they would only inflate the assumption count without progress.
