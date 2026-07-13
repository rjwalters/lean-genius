# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 23 available, 562 in-progress, 1407 completed, 3 graduated, 1 blocked

## Selected Problem

- **ID**: triangle-angle-sum-oq-02
- **Name**: Triangle Angle Sum: Gauss-Bonnet Theorem Formalization in Lean
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among unclaimed EMPTY candidates (68)**: With all
   available problems at EMPTY knowledge tier (0 items), composite reduces to
   `(tractability × 10) + significance`. Score 68 ties with
   `szemeredi-regularity-oq-02` but differential geometry is underrepresented
   in recent batch selections (dominated by algebra, economics, additive
   combinatorics, lattice geometry).

2. **Domain diversity**: Batch selections today were:
   - `liouville-theorem-oq-04` — p-adic complex analysis
   - `shapley-folkman-oq-03` — convex analysis / economics
   - `erdos-476-oq-05-wip-01` — additive combinatorics (Cauchy-Davenport)
   - `solution-of-cubic-oq-05` — classical algebra / Galois
   - `minkowski-fundamental-theorem-oq-04` — lattice geometry / number theory

   Riemannian/differential geometry is absent. `triangle-angle-sum-oq-02`
   (Gauss-Bonnet) fills this gap — no diversity penalty applies.

3. **Strategic depth**: The gallery has `triangle-angle-sum` (Euclidean angle
   sum, verified) and `triangle-angle-sum-oq-01` (converse, verified). Gauss-Bonnet
   is the natural capstone of this family, connecting the elementary Euclidean
   result to its deep topological generalisation via Euler characteristic.

4. **Tractable entry point**: The full Gauss-Bonnet theorem requires
   differential geometry infrastructure not yet in Mathlib. However, the
   discrete Descartes/Gauss-Bonnet theorem (total angle defect of a convex
   polyhedron = 4π) is fully combinatorial and achievable with current Mathlib.
   A researcher can deliver a genuine Gauss-Bonnet result without needing
   differential geometry primitives.

## Ranking Summary (top EMPTY candidates)

| ID | Sig | Tract | Composite | Decision |
|----|-----|-------|-----------|----------|
| **triangle-angle-sum-oq-02** | **8** | **6** | **68** | **SELECTED** (diversity tiebreak) |
| szemeredi-regularity-oq-02 | 8 | 6 | 68 | Tied; Szemerédi family already has 4 available |
| newton-inductive-step-oq-03 | 7 | 6 | 67 | Slightly lower significance |
| ptolemys-complex-proof-oq-02 | 7 | 6 | 67 | Slightly lower significance |
| ptolemys-theorem-oq-01-oq-02 | 7 | 6 | 67 | Slightly lower significance |
| szemeredi-counting-oq-02 | 8 | 5 | 58 | Lower tractability |
| sylow-theorem-oq-02 | 7 | 5 | 57 | Lower composite |
| szemeredi-full-oq-01 | 9 | 4 | 49 | Furstenberg ergodic — high ambition, tractability 4 |
| isoperimetric-theorem-oq-03 | 8 | 4 | 48 | Best constants non-Euclidean — tractability 4 |
| hurwitz-theorem-oq-04 | 7 | 4 | 47 | Exceptional Lie groups — tractability 4 |

Moonshot problems (weak-goldbach, twin-primes, sophie-germain, tractability ≤ 2)
excluded from serious consideration.

## Rejection Summary

- **Candidates considered**: 23 (all available from pool)
- **Candidates rejected**: 22
  - Moonshot tier (tractability ≤ 2): weak-goldbach, twin-primes-special, sophie-germain
  - Szemerédi family (4 problems): kept for future cycles to avoid over-concentration
  - `erdos-476-oq-05-wip-01`: already claimed (active lock)
  - `triangle-angle-sum-oq-03`: already claimed (active lock)
  - Remaining: all outranked by composite score or diversity consideration
- **Confidence**: high — tiebreaker applied on well-understood grounds

## Related Gallery Proofs

- `triangle-angle-sum`: Direct predecessor — Euclidean angle sum π already proved.
  The Gauss-Bonnet theorem is the geometric generalisation.
- `triangle-angle-sum-oq-01`: Converse result — parallel postulate ↔ angle sum π.
  Open questions there explicitly mention the Gaussian curvature connection.
- `spherical-law-of-cosines`: Spherical geometry infrastructure exists in gallery.
  The spherical excess formula (angle sum > π on S²) is a special case of Gauss-Bonnet.
- `napoleons-theorem`: Recent complex-number geometry — demonstrates Lean 4 geometric
  reasoning at comparable difficulty.

## Suggested First Steps

1. **OBSERVE**: Audit Mathlib for relevant infrastructure:
   - Search `Mathlib.Geometry.Manifold.*` for Riemannian/smooth manifold support
   - Search `Mathlib.Combinatorics.*` for Euler characteristic / polyhedron theorems
   - Check for `EulerCharacteristic`, `gaussBonnet`, `GaussianCurvature` in Mathlib4
   - Read `proofs/Proofs/SphericalLawOfCosines.lean` for spherical geometry API in use

2. **ORIENT**: Assess the discrete vs. continuous fork:
   - If Euler's formula $V - E + F = 2$ is in Mathlib → discrete Descartes theorem tractable
   - If spherical geodesic infrastructure exists → spherical excess formula tractable
   - If neither → formalize the theorem statement with axioms for missing infrastructure
   - Scout survey: what differential geometry results closest to Gauss-Bonnet exist in Lean?

3. **DECIDE**: Choose scope based on ORIENT findings:
   - **Primary target**: Discrete Gauss-Bonnet (Descartes' theorem for polyhedra:
     $\sum_v (2\pi - \text{angle sum at } v) = 4\pi$ for convex polyhedra)
   - **Secondary target**: Spherical excess formula for triangles on $S^2$
   - **Stretch goal**: Full local Gauss-Bonnet as an axiomatized statement with
     commentary on required Mathlib infrastructure

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 23 |
| In Progress | 562 |
| Completed | 1407 |
| Graduated | 3 |
| Blocked | 1 |
| **Total** | **1996** |

## Candidate Pool Health

Pool has 23 available problems — above the 15-problem minimum threshold.

- **Pool depth**: adequate (23 available vs. 15 threshold)
- **Recommendation**: Pool healthy. Szemerédi family (4 problems), moonshots (3),
  and B/C tier tractable problems provide good variety. No immediate replenishment needed.
- **Next refresh recommended**: When available count drops below 15, or after 8
  more selections exhaust the current tractable tier.

## Initialized

- [x] Research workspace registered in `research/db/knowledge.db`
- [x] `candidate-pool.json` regenerated via `sync_pool.py`
- [x] Research workspace at `research/problems/triangle-angle-sum-oq-02/` ready
- [ ] Ready for /researcher
