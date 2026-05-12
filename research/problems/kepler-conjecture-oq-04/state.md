# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-5): Initial survey of `kepler-conjecture-oq-04` —
optimal packing density for non-spherical objects (ellipsoids,
tetrahedra, general convex bodies) in ℝ³.

The parent gallery proof `kepler-conjecture` axiomatizes the
Kepler-Hales theorem for **congruent spheres**, but says nothing
about other convex bodies. OQ-04 spans the natural generalisations:

1. **Tetrahedral packing** — best known `δ ≥ 4000/4671 ≈ 0.8564`
   (Chen–Engel–Glotzer 2010), STRICTLY ABOVE the FCC sphere density
   `π/(3√2) ≈ 0.7405`.
2. **Ellipsoid packing** — best known `δ ≈ 0.7707` at aspect ratio
   `α ≈ √2` (Donev–Stillinger–Chaikin–Torquato 2004); lattice-only
   case exactly equals `π/(3√2)` (Bezdek–Kuperberg 2007).
3. **General convex bodies** — Ulam's conjecture (1972, open) says
   every symmetric convex body in ℝ³ packs `δ ≥ π/(3√2)`. The unit
   ball would be the LEAST dense convex body to pack.

## Active Approach

**Tetrahedral refutation first — axiom-free deliverable.**

The cleanest formalizable result is `4000/4671 > π/(3√2)` — a pure
real-number numerical computation provable using `Real.pi_sq_lt`
without any new axioms. This establishes that the parent's
`PackingDensity` type admits values strictly above `fccDensity`,
demonstrating that the Kepler upper bound is **shape-specific**
(spheres only) rather than universal.

The ellipsoid and Ulam statements (S5/S6) are deferred to later
sessions and require axiomatization, since their proofs are
respectively (a) a substantial published theorem (Bezdek–Kuperberg)
and (b) genuinely open since 1972 (Ulam).

## Blockers

None mathematical. Practical: the `proofs/.lake` symlink is broken in
researcher worktrees (~25-45 min cost per Docker build). S2 is short
enough that one end-of-S2 Docker build is feasible.

## Next Action

**S2 (next researcher session)**: Create new file
`proofs/Proofs/KeplerConjectureOQ04.lean` with:

```lean
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pi.Bounds
import Proofs.KeplerConjecture

namespace KeplerConjectureOQ04

open Real KeplerConjecture

/-- Chen–Engel–Glotzer dimer packing density for regular tetrahedra in ℝ³. -/
noncomputable def tetrahedronDimerDensity : ℝ := 4000 / 4671

theorem tetrahedronDimerDensity_pos : 0 < tetrahedronDimerDensity := by
  unfold tetrahedronDimerDensity; norm_num

theorem tetrahedronDimerDensity_lt_one : tetrahedronDimerDensity < 1 := by
  unfold tetrahedronDimerDensity; norm_num

end KeplerConjectureOQ04
```

Verify with Docker build (`./proofs/scripts/docker-build.sh
Proofs.KeplerConjectureOQ04`) at the end of S2; ~25-45 min wall-clock
with the broken `.lake` symlink.

**S3 (next session after S2)**: Add the numerical inequality
`tetrahedronDimerDensity_gt_fccDensity` using `div_lt_div_iff`,
`Real.sq_sqrt`, and `Real.pi_sq_lt`. Estimated ~50 lines.

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 1
- Approaches tried: 1

## Open files

- `problem.md` — Plain statement, why-it-matters, Mathlib infrastructure
  map, S2-through-S7 decomposition, risk notes, references.
- `knowledge.md` — S1 session note: tetrahedral refutation arithmetic
  (worked out in detail), Ulam conjecture context, worked numerics,
  Mathlib gap inventory, next-action priority table.

## S1 Deliverable

This iteration is **survey-only**:

- 0 new theorems
- 0 new sorries
- 0 axioms touched
- 0 `.lean` files created

Substantive output: `problem.md` (Mathlib API map + suggested S2-S7
decomposition + risk notes + references) and `knowledge.md` (math
content of all three flagship sub-questions, the worked-out tetrahedral
arithmetic with detailed steps and margin calculations, Ulam-vs-Kepler
duality observation, and Mathlib gap inventory).

Ready hand-off for the S2 implementer.
