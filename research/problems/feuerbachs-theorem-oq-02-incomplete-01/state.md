# Research State: feuerbachs-theorem-oq-02-incomplete-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-05-02T00:50:00Z
**Iteration**: 3
**LastUpdate**: 2026-05-02

## Current Focus
Refutation of the candidate (N₂₄, R/3)-Feuerbach sphere via closed-form
counterexample at the orthocentric tetrahedron T₀ = ((2,0,0),(0,3,0),
(0,0,6),(0,0,0)). Five sorry-stated tangency theorems and the bundled
`feuerbach_3d_theorem` removed; 5 sorries → 0; 1 axiom unchanged.

## Active Approach
Refutation has replaced the original "prove these five tangency theorems"
program. The next research direction is identifying and formalizing the
correct 3D Feuerbach sphere (Murakami 1952 face-circumcircle construction
or Court 1934 isodynamic version).

## Attempt Count
- Total attempts: 3
- Current approach attempts: 1 (refutation)
- Approaches tried:
  1. Single-tactic proofs of routine helpers (Aristotle companion).
  2. Removal of two false axioms (`edge_midpoints_on_sphere`,
     `face_centroids_on_sphere`); proved
     `edge_midpoints_equidist_from_centroid` instead.
  3. Closed-form refutation of the (N₂₄, R/3)-sphere candidate;
     removal of 5 sorry-stated tangency theorems.

## Blockers
- Constructing a Lean witness for `feuerbach_3d_fails_general` (or for
  the explicit refutation `∃ T : OrthocentricTetrahedron, ¬ tangent`)
  requires √14 arithmetic. Mathlib's `nlinarith`/`polyrith` don't yet
  handle algebraic numbers transparently.
- Formalizing the correct (Murakami / Court) Feuerbach sphere requires
  new infrastructure for face circumcircles in ℝ³ and the associated
  tangency relations — likely 200–500 lines of new code.

## Next Action
1. Survey Murakami (1952) and Court (1934) to extract the precise
   center / radius formulas for the correct 3D Feuerbach sphere, and
   record them in `problem.md` for a future session.
2. Optionally promote the refutation to a Lean theorem
   `∃ T : OrthocentricTetrahedron, ¬ spheresInternallyTangent ...`
   once a √-arithmetic tactic is available.
3. Investigate whether the 24-point sphere actually passes through
   the 24 named points (edge midpoints, face centroids, altitude
   feet, midpoints of vertex–orthocenter segments). The
   midedge-only result is proved; the rest are unverified and the
   classical name "twenty-four-point sphere" may itself be a
   misnomer with these definitions.
