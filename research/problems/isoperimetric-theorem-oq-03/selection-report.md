# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 26 available, 557 in-progress, 1408 completed, 3 graduated, 2 blocked

## Selected Problem

- **ID**: isoperimetric-theorem-oq-03
- **Name**: Isoperimetric Theorem: Best Constants in Non-Euclidean Spaces
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 4/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Composite score 48** — second among genuinely unselected candidates. The domain
   (differential geometry / geometric analysis) is the only one of its kind among
   remaining unselected problems, providing domain diversity for the batch.

2. **A-tier significance** — the isoperimetric problem in non-Euclidean spaces connects
   Riemannian geometry, comparison theory (Bishop-Gromov, Lévy-Gromov), and optimal
   transport. The Lévy-Gromov inequality for Ricci-positive manifolds is a deep result
   from Gromov's 1980 work. A formal statement in Lean 4 would complement the existing
   `isoperimetric-theorem` and `isoperimetric-theorem-oq-01` gallery proofs.

3. **Clear parent chain** — the gallery already has the Euclidean case and the
   curved-surface extension. This problem extends to general Riemannian manifolds with
   curvature bounds. Tractability is 4 because Mathlib lacks full Riemannian geometry
   infrastructure, but stating the theorem with `sorry` and proving the hyperbolic plane
   special case partially is achievable.

4. **Domain diversity** — only pure differential geometry / geometric analysis candidate
   among the remaining 7 unselected problems. Represents an underrepresented area
   in the research pipeline.

## Rejection Summary

- **Candidates considered**: 7 remaining unselected available problems
- **Moonshot candidates rejected**: twin-primes-special-oq-01, weak-goldbach-oq-01,
  sophie-germain-oq-01 (tractability ≤ 2)
- **szemeredi-full-oq-01**: deferred — third Szemerédi problem would dominate the batch;
  the Furstenberg ergodic approach is better in a future cycle
- **Confidence**: medium — the non-Euclidean isoperimetric problem is difficult, but
  the hyperbolic plane special case via `sinh`/`cosh` identities is tractable

## Related Gallery Proofs

- `isoperimetric-theorem`: Parent Euclidean isoperimetric theorem — 4πA ≤ L² with
  equality for disks. Area/perimeter formalization infrastructure.
- `isoperimetric-theorem-oq-01`: Shapes on other surfaces — extends to curved 2-surfaces.
  Direct predecessor of this non-Euclidean generalization.
- `triangle-angle-sum-oq-02`: Gauss-Bonnet theorem formalization — angle-sum in curved
  spaces; relevant infrastructure for Riemannian geometry arguments.

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/IsoperimetricTheorem.lean` and `IsoperimetricTheoremOQ01`
   to understand formalization of area, perimeter, and the isoperimetric inequality on
   curved surfaces. Check what Riemannian geometry Mathlib provides
   (`Mathlib.Geometry.RiemannianManifold`, `Mathlib.Analysis.InnerProductSpace`).

2. **ORIENT**: Scope to the hyperbolic plane ℍ² first. In ℍ², the isoperimetric
   inequality is `L² - 4πA ≥ A²` (sharper than Euclidean). Extremal sets are geodesic
   disks. Survey `Mathlib.Geometry.Hyperbolic` for geodesic ball area/length formulas.

3. **DECIDE**: State the Lévy-Gromov inequality as a `sorry`-bearing theorem and prove
   the ℍ² specialization by direct computation. Geodesic disk of radius r in ℍ²:
   area = `4π sinh²(r/2)`, perimeter = `2π sinh(r)`. Then `L² - 4πA` reduces to a
   `sinh`/`cosh` identity provable by `nlinarith` after unfolding hyperbolic trig
   definitions.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 26 |
| In Progress | 557 |
| Completed | 1408 |
| Graduated | 3 |
| Blocked | 2 |

## Candidate Pool Health

- Pool depth: **adequate** (26 available, threshold=15)
- Recommendation: Pool healthy.
- Next refresh recommended: next scheduled cycle (~30 min)

## Initialized

- [x] Research workspace exists (`research/problems/isoperimetric-theorem-oq-03/`)
- [x] problem.md populated
- [x] state.md: OBSERVE phase
- [x] Ready for /researcher
