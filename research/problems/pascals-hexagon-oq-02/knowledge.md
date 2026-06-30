# Knowledge Base: pascals-hexagon-oq-02

Open question of the parent gallery entry `pascals-hexagon`:

> Derive **Brianchon's theorem** — the three main diagonals of a hexagon
> *circumscribed* about a conic are concurrent — as the projective dual of the
> already-formalized Pascal hexagon theorem.

---

## Status: RESOLVED (2026-06-15)

Fully answered by **PR #24657** (merged): `proofs/Proofs/PascalsHexagonOQ02.lean`
(199 lines, 7 theorems, 7 definitions, **0 axioms, 0 sorries**), registered in
`proofs/Proofs.lean`. Gallery `meta.json` + `annotations.json` present under
`src/data/proofs/pascals-hexagon-oq-02/`. Main result `brianchon_theorem`
(file line 177), packaged as `brianchon_circumscribed` (line 189).

Do **not** re-survey or re-derive — this OQ is complete. Future claims of this
slug should either verify the build in a quiet window or move to the adjacent
open directions below.

---

## Insights — why the duality proof is clean (no symmetry argument needed)

The parent `PascalsHexagon.lean` models ℝP² by nonzero vectors in ℝ³, in which
**projective duality is built into the representation**:

- the **join** of two points and the **meet** of two lines are the *same*
  operation (`crossProduct`), so `lineThrough = lineIntersection`;
- `collinear` and `concurrent` are the *same* determinant predicate
  `det(·,·,·) = 0`.

Consequently the configuration is **self-dual** and Brianchon needs no separate
symmetry lemma. The derivation:

1. A line is tangent to a point-conic `C` iff (as a vector) it lies on the dual
   conic `dualConic C = adj C` (`side_tangent_iff_on_dualConic`, line 196;
   `dualConic_symmetric`, line 72).
2. The six tangent sides of a circumscribed hexagon are therefore six points
   *inscribed* in the dual conic (`toInscribed`, line 131).
3. `pascal_hexagon_theorem` applied to that inscribed hexagon makes its three
   opposite-side intersection points collinear; those points are
   **definitionally** the three main diagonals of the circumscribed hexagon —
   `pascalP/Q/R_toInscribed` (lines 154–160) close by `rfl`.
4. Collinearity of three lines = concurrency, giving Brianchon.

Key takeaway for any dual-conic work in this model: opposite-side/diagonal
correspondences collapse to `rfl` because join≡meet and collinear≡concurrent,
so the "dual" theorem is the *same* theorem read on `adj C`.

---

## Adjacent open directions (genuinely deeper — not cosmetic variants)

These would be new work, not duplication of the resolved OQ-02:

1. **Braikenridge–Maclaurin converse.** If the three opposite-side intersection
   points of a hexagon are collinear, the six vertices lie on a conic — the
   converse of Pascal. A genuine strengthening (constructive/converse), not a
   dual restatement.
2. **Hexagrammum Mysticum / 60-line configuration.** The full combinatorial
   structure of the 60 Pascal lines (Steiner points, Plücker lines, Kirkman
   points). Active under the sibling `pascals-hexagon-oq-03` line of work
   (`PascalsHexagonOQ03.lean`, `DihedralGroup 6 ≃* hexagonalGroup`).
3. **Degenerate conics (pairs of lines).** Pappus's theorem as the line-pair
   degeneration of Pascal — check whether the ℝ³ model specializes cleanly.

## Dead Ends / Non-starters

- Re-proving Brianchon by an independent symmetry/transpose argument:
  unnecessary in this model (join≡meet makes it the same determinant identity).
