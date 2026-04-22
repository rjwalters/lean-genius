# Problem Selection Report

**Date**: 2026-04-22
**Mode**: SELECT
**Pool Status**: 25 available, 561 in-progress, 1404 completed, 3 graduated, 1 blocked

## Selected Problem

- **ID**: triangle-angle-sum-oq-02
- **Name**: Triangle Angle Sum: Gauss-Bonnet Theorem Formalization in Lean
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among unclaimed EMPTY candidates (68)**: With all 25
   available problems at EMPTY knowledge tier (0 items), composite reduces to
   `(tractability × 10) + significance`. Score 68 leads the field by 10 points
   over the next-best unclaimed candidates (szemeredi-counting-oq-02 at 58,
   sylow-theorem-oq-02 at 57).

2. **EMPTY knowledge tier**: No prior research has accumulated in this workspace —
   fresh territory, workspace initialized today (2026-04-22), 0 attempts.

3. **Domain diversity**: The last 5 seeker selections were:
   - `sqrt2-minpoly` — algebraic number theory
   - `shapley-folkman-oq-03` — convex analysis / economics
   - `newton-inductive-step-oq-03` — combinatorics / q-analogues
   - `napoleons-theorem-oq-02` — classical geometry / DFT
   - `sqrt2-plus-sqrt3-irrational-oq-03` — algebraic number theory

   Differential geometry is unrepresented in recent selections. `triangle-angle-sum-oq-02`
   brings Gauss-Bonnet / Riemannian geometry into the research pipeline — no diversity
   penalty applies.

4. **Strategic depth**: The gallery already has `triangle-angle-sum` (Euclidean angle sum,
   verified), `triangle-angle-sum-oq-01` (converse, verified), `spherical-law-of-cosines`,
   and `spherical-law-of-sines`. Gauss-Bonnet is the natural capstone of this family,
   connecting the elementary Euclidean result to its deep topological generalisation.

5. **Tractable entry point**: The full Gauss-Bonnet theorem requires significant new
   Mathlib infrastructure (geodesic curvature, connection forms). However, the discrete
   Descartes/Gauss-Bonnet theorem (relating angle defects at polyhedron vertices to the
   Euler characteristic) is fully combinatorial and achievable with current Mathlib.
   A researcher can deliver a genuine Gauss-Bonnet result without needing differential
   geometry primitives.

## Ranking Summary (top EMPTY candidates)

| ID | Sig | Tract | Composite | Decision |
|----|-----|-------|-----------|----------|
| **triangle-angle-sum-oq-02** | **8** | **6** | **68** | **SELECTED** |
| szemeredi-counting-oq-02 | 8 | 5 | 58 | Runner-up; Szemerédi overrepresented |
| sylow-theorem-oq-02 | 7 | 5 | 57 | Computational complexity framing; lower sig |
| divisibility-truncation-general-oq-03 | 6 | 5 | 56 | Lower significance |
| szemeredi-full-oq-01 | 9 | 4 | 49 | Furstenberg ergodic — high ambition, tractability 4 |
| isoperimetric-theorem-oq-03 | 8 | 4 | 48 | Best constants non-Euclidean — tractability 4 |
| hurwitz-theorem-oq-04 | 7 | 4 | 47 | Exceptional Lie groups — tractability 4 |

Moonshot problems (weak-goldbach, twin-primes, sophie-germain, tractability ≤ 2)
excluded from serious consideration.

## Rejection Summary

- **Candidates considered**: 25 (all available from pool)
- **Candidates rejected**: 24
  - Moonshot tier (tractability ≤ 2): weak-goldbach, twin-primes-special, sophie-germain
  - Szemerédi family (4 problems): kept for future cycles to avoid over-concentration
  - Remaining: all outranked by composite score
- **Confidence**: high — 10-point gap between selected (68) and runner-up (58)

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
| Available | 25 |
| In Progress | 561 |
| Completed | 1404 |
| Graduated | 3 |
| Blocked | 1 |
| **Total** | **1994** |

## Candidate Pool Health

Pool has 25 available problems — above the 15-problem minimum threshold.

- **Pool depth**: adequate (25 available vs. 15 threshold)
- **Recommendation**: Pool healthy. Szemerédi family (4 problems), moonshots (3), and
  B/C tier tractable problems provide good variety. No immediate replenishment needed.
- **Next refresh recommended**: When available count drops below 15, or after 5–6
  more selections exhaust the current tractable tier

## Initialized

- [x] Research workspace registered in `research/db/knowledge.db`
- [x] `src/data/research/problems/triangle-angle-sum-oq-02.json` registered
- [ ] Ready for /researcher
