# Knowledge Base: brianchon-theorem-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Brianchon's theorem (1806): a hexagon circumscribed about a conic (all six sides
tangent) has its three main diagonals concurrent. It is the exact projective
dual of Pascal's hexagon theorem (1639), which is already formalized in the
gallery (`pascals-hexagon`, `PascalsHexagon.lean`). Pascal: hexagon *inscribed*,
opposite-side intersections *collinear*. Brianchon: hexagon *circumscribed*,
main diagonals *concurrent*. Duality swaps points↔lines and collinear↔concurrent.

---

## Insights

- **The gallery's projective model is self-dual.** In `PascalsHexagon.lean`,
  points and lines are nonzero vectors in ℝ³, join/meet are both the cross
  product, and `collinear`/`concurrent` are *the same* predicate
  `(threeVectorMatrix · · ·).det = 0`. So duality is just relabelling vectors.

- **One computational identity drives the whole duality.** The cofactor /
  Binet–Cauchy identity `(M·u)×(M·v) = (adj M)ᵀ·(u×v)` (a degree-3 polynomial
  identity, closed by `ring` once `Matrix.adjugate_fin_three` expands the 3×3
  adjugate). PascalsHexagon already proves this as `crossProduct_projTransform`;
  we reprove a clean standalone version `crossProduct_mulMatrix`.

- **Each Brianchon diagonal = (det C • C) applied to the matching Pascal point.**
  For a symmetric conic C, the tangent at a contact point P is the polar C·P.
  A circumscribed-hexagon vertex is `(C·P)×(C·Q) = (adj C)·(P×Q)` (using
  symmetry: `(adj C)ᵀ = adj C`). A diagonal joins two such vertices, so applying
  the identity again gives `adj(adj C)·(Pascal point)`. For 3×3,
  `adjugate (adjugate C) = det C • C` (Mathlib `adjugate_adjugate`, exponent
  card−2 = 1). Hence each diagonal is `(det C • C)·(Pascal point)`.

- **Determinant transport closes it with no nondegeneracy needed.** Since
  `det(M·u, M·v, M·w) = det M · det(u,v,w)`, the Brianchon triple determinant is
  `det(det C • C)` times the Pascal triple determinant. Pascal collinearity ⟹
  the Pascal determinant is 0 ⟹ product is 0 ⟹ Brianchon concurrency — even
  without assuming `det C ≠ 0`.

- **No new axiom.** `concurrent_brianchon_of_collinear_pascal` (the bridge) is
  axiom-free and sorry-free (`#print axioms`: propext, Classical.choice,
  Quot.sound only). `brianchon_theorem` adds exactly `conic_implies_pascal`, the
  same fact `pascals-hexagon` already assumes. This answers an open question the
  Pascal entry itself recorded.

## Built Items

- `proofs/Proofs/BrianchonTheorem.lean` (293 lines, builds clean, 0 sorries):
  - `crossProduct_mulMatrix` — cofactor cross-product identity (ring).
  - `det_threeVectorMatrix_mulMatrix` — determinant transport.
  - `dual_matrix_eq` — `((adj C)ᵀ adj)ᵀ = det C • C` for symmetric 3×3.
  - `diag_eq` — each diagonal = (det C • C)·(Pascal point).
  - `concurrent_brianchon_of_collinear_pascal` — axiom-free duality bridge.
  - `brianchon_theorem` — unconditional Brianchon (1 axiom).
- Gallery entry `src/data/proofs/brianchon-theorem-oq-01/meta.json`.

## Mathlib Gaps

- Mathlib has no off-the-shelf `(M·u)×(M·v) = (adj M)ᵀ·(u×v)`; proved locally by
  `ring` via `adjugate_fin_three`. (Candidate for upstreaming.)

## Why self-contained (not `import Proofs.PascalsHexagon`)

`PascalsHexagon.lean` currently has a hard build error in its WIP Sylvester
section (`associated (R := ℝ)` — invalid argument name) plus a known `sorry`, so
it cannot be imported. `BrianchonTheorem.lean` therefore redefines the minimal
projective model and restates the Pascal fact as its own axiom
`conic_implies_pascal` (identical in content). This keeps the proof
independently verifiable.

---

## Dead Ends

- Importing `Proofs.PascalsHexagon` to reuse its `projTransform` /
  `crossProduct_projTransform` / `conic_implies_pascal_constraint`: blocked by
  the pre-existing hard build error in that file (Sylvester section). Resolved
  by going self-contained.

---

## Sessions

## Session 2026-06-19 (Session 2) — Brianchon proved via Pascal duality

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Surveyed `PascalsHexagon.lean`; found its self-dual ℝ³ model and the existing
  cofactor/determinant-transport lemmas.
- Designed the pole–polar reduction: diagonal = (det C • C)·(Pascal point).
- Discovered `PascalsHexagon.lean` does not build (Sylvester-section error);
  pivoted to a self-contained file.
- Wrote and machine-verified `BrianchonTheorem.lean` (0 sorries); confirmed the
  axiom budget with `#print axioms`.
- Added gallery `meta.json`; advanced phase to COMPLETED.

### Key Findings
- The duality bridge is genuinely axiom-free; only Pascal's own fact is assumed.
- No nondegeneracy hypothesis is needed for the concurrency conclusion.

### Files Modified
- proofs/Proofs/BrianchonTheorem.lean (new)
- proofs/Proofs.lean (import)
- src/data/proofs/brianchon-theorem-oq-01/meta.json (new)
- research/problems/brianchon-theorem-oq-01/{state.md, knowledge.md}
- src/data/research/problems/brianchon-theorem-oq-01.json (new)

### Next Steps
- Eliminate the shared `conic_implies_pascal` axiom (Pascal-side work).
- Optionally add nondegeneracy to recover the genuine Brianchon point.

## Session 2026-06-19 (Session 3) — Discharge strategy for the Pascal axiom; Aristotle staged

**Mode**: REVISIT (advancing nextStep #1: eliminate `conic_implies_pascal`)
**Outcome**: progress (strategy + infrastructure; 0 sorries eliminated — Aristotle service down)

### What I Did
- Localized the axiom-elimination frontier precisely: in `PascalsHexagon.lean`,
  `sylvester_stdConic_of_isotropic` is the *only* remaining `sorry` on the
  documented elimination path — `proof_sketch_conic_implies_pascal`,
  `pascal_std_conic`, `pascalConstraint_projTransform`, and the Mathlib
  QuadraticForm bridge (`mathlibQF_separatingLeft`) are all complete.
- **Numerically tested the axiom across conic ranks** (200k+ random hexagons):
  rank-1 double line `diag(1,0,0)`, rank-2 line pair `diag(1,-1,0)`, standard
  `diag(1,1,-1)`, and random nondegenerate symmetric `C`. Normalized
  `det(P,Q,R)` residuals 1e-9 … 1e-28 in every case.
- Created and build-verified `proofs/Proofs/BrianchonTheoremAristotle.lean`
  (self-contained, exactly one `sorry`, docker build GREEN) — the full general
  Pascal collinearity as a provable theorem, carrying the corrected proof
  strategy as its docstring hint.
- Attempted Aristotle submission (`prove` and `prove_file`, MCP) — service
  returned `Resource not found` for every call incl. a trivial connectivity
  probe. **Aristotle is down this session**; companion is staged for submission
  when it returns.

### Key Findings
- **`conic_implies_pascal` (determinant form) is a universal polynomial
  identity.** It holds for *every* symmetric conic `C` — degenerate included —
  with NO nondegeneracy or point-validity hypothesis. So the gallery axiom is
  *sound as stated* (no missing-hypothesis bug), and `det(P,Q,R)` lies in the
  ideal generated by the six conic equations `conicQuadraticForm C p_k = 0`.
- **Discharge does NOT require Sylvester's law.** The scaffolded route in
  `PascalsHexagon.lean` (Sylvester reduction to the standard conic, needing
  nondegeneracy + a real point) is sufficient but *not necessary*. A direct
  ideal-membership / `linear_combination` proof in the six quadratic hypotheses
  should exist and is preferable — it is self-contained and, unlike the
  Sylvester route, does not depend on repairing `PascalsHexagon.lean` (which
  still has a hard build error in its WIP Sylvester section). Cofactors are
  degree ≈10 polynomials in the 18 coordinates + entries of `C`; `polyrith` /
  Aristotle should find them.

### Files Modified
- proofs/Proofs/BrianchonTheoremAristotle.lean (new; build-verified, 1 sorry)
- research/problems/brianchon-theorem-oq-01/knowledge.md
- src/data/research/problems/brianchon-theorem-oq-01.json

### Next Steps
- When Aristotle is back: submit `BrianchonTheoremAristotle.lean` (hint already
  in docstring) and/or the isolated `sylvester_stdConic_of_isotropic`.
- Try a direct `linear_combination`/`polyrith` proof of `conic_implies_pascal`
  from the six `pointOnConic` hypotheses (the polynomial-identity route).
- Once discharged, replace the axiom in `BrianchonTheorem.lean` with the theorem
  and drop the `axiom` from the entry (status verified for the Brianchon side).
