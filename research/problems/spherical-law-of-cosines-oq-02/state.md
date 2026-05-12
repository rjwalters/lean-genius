# Research State: spherical-law-of-cosines-oq-02

## Current State
**Phase**: OBSERVE (S1 complete)
**Path**: full
**Since**: 2026-05-12 ~22:48 UTC
**Iteration**: 1 (S1)

## Current Focus

S1 OBSERVE — Girard–Euler theorem (spherical excess formula) roadmap via the
lune-decomposition proof (Lhuilier 1782).

Deliverable: `sessions/2026-05-12-s1-observe-lune-decomposition-roadmap.md` (this PR).
Confirms that the parent `Proofs.SphericalLawOfCosines` provides the unit-vector /
inner-product foundation, but **no spherical-area definition**. Maps three S2 sub-
iterations (S2a/b/c, ~250 LOC) on the lune-decomposition path. Notes that the in-tree
`Proofs.TriangleAngleSumOQ02.girard_theorem` exists but is axiomatized (built on a
structure-encoded `gb_local` field), so it does not satisfy this OQ's
from-first-principles requirement.

## Active Approach

S1 OBSERVE: literature + Mathlib API survey + roadmap. No Lean code touched.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (S1 OBSERVE)

## Blockers

**Potential Mathlib gap** (to verify at S2a): Mathlib v4.26.0 does not obviously have a
canonical `Measure (Sphere ℝ³ 1)` matching the standard $S^2$ surface measure. Possible
workarounds:
1. Push forward `volume` from $\mathbb{R}^3$ via a chart — but this isn't a surface
   measure.
2. Pull back from $\mathbb{R}^2$ via stereographic projection or spherical coordinates —
   ergonomic but requires `MeasureTheory.measurableHomeomorph` + Jacobian.
3. Define solid-angle directly: $\Omega(\triangle) := \mu(\text{Cone}(\triangle) \cap B(0, 1))$
   where Cone is the cone of rays from origin into the triangle. Reduces sphere measure
   to 3-D Lebesgue measure restricted to a cone — uses standard `MeasureTheory.volume`.

**Recommendation for S2a implementer**: use option 3 (solid-angle definition). It avoids
all spherical-measure infrastructure questions and reduces the problem to a 3-D
Lebesgue measure computation. The lune is then a cone-cap whose volume measure is
$\frac{1}{3} \cdot \mu(\text{spherical cap part})$, etc.

## Next Action

**S2a ACT**: write `proofs/Proofs/SphericalLawOfCosinesOQ02.lean` with:
- `def solidAngle (u v w : EuclideanSpace ℝ (Fin 3)) : ℝ` (option 3 above; via
  `MeasureTheory.volume` on the cone in $\mathbb{R}^3$).
- `def lune (u v : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) : Set (EuclideanSpace ℝ (Fin 3))`
- `lemma lune_solidAngle_eq_two_theta`.

~80 LOC, 0 sorries (target). Verify option 3 works at S2a time.

## Open PRs
- This PR (S1 OBSERVE doc-only — ~+650 LOC across problem.md, state.md, knowledge.md,
  and `sessions/2026-05-12-s1-observe-lune-decomposition-roadmap.md`).

## Iteration History (recent)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-5 | (this PR) | OBSERVE — Lhuilier lune-decomposition roadmap, 3-sub-iteration S2 plan (~250 LOC), spherical-measure gap flagged |
