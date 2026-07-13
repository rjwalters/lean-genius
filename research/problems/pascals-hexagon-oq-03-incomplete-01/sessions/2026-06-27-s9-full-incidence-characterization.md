# S9 — Full Incidence Characterization of the Pascal Line (researcher-6)

**Date:** 2026-06-27
**Phase:** ACT (incidence layer, exhaustive characterization)
**Entry:** pascals-hexagon-oq-03-incomplete-01
**File:** `proofs/Proofs/PascalsHexagonOQ03.lean` — **PART 4k**

## What was added (0 sorry / 0 new axiom)

PART 4h proved the *three* incidences `P, Q, R ∈ pascalProjLine` using only the
forward direction `pointOnLine_cross_of_collinear : collinear p q r →
pointOnLine r (p ×₃ q)`. That direction identifies the three known Pascal
points but is silent about every *other* point of the line. PART 4k closes the
gap with the missing **converse** and packages the *iff*:

- `collinear_of_pointOnLine_cross (p q r)` — `pointOnLine r (p ×₃ q) →
  collinear p q r`. The incidence `r · (p ×₃ q) = 0` is, monomial for monomial,
  the determinant `det(p, q, r) = 0` (scalar triple product = determinant, by
  the cyclic symmetry of `det`), so the converse uses the **same**
  `linear_combination` certificate as the forward lemma — no nondegeneracy.
- `pointOnLine_cross_iff_collinear (p q r)` — the bundled iff
  `pointOnLine r (p ×₃ q) ↔ collinear p q r`. The fundamental "a point lies on
  the join of `p, q` iff the three are collinear."
- `pointOnLine_pascalProjLine_iff_collinear hex r` — the geometric payoff:
  `pointOnLine r (pascalProjLine hex) ↔ collinear (pascalP hex) (pascalQ hex) r`.
  Characterizes the **entire** Pascal line as a point set — *exactly* the locus
  of points collinear with the two spanning Pascal points `P, Q` — strengthening
  the three-point incidence of PART 4h to an exhaustive description. Taking
  `r = R` recovers `pascalR_on_pascalProjLine` via Pascal's theorem.

## Why this is genuine

The repo previously had only the one-directional incidence. The converse is the
honest statement "every point on the line is collinear with the spanning pair,"
which is what lets one *reason backwards* from line membership — needed for any
future Steiner/Kirkman concurrence argument (a Kirkman/Steiner point is defined
by lying on several Pascal lines, i.e. by collinearity with each line's spanning
pair). Unconditional: no `hnd` general-position hypothesis.

## Out of scope (unchanged)

`steiner_count_eq_20`, `kirkman_count_eq_60` (OQ-03-OQ-03/04) — genuinely open
Conway–Ryba concurrence combinatorics; and the `hnd` general-position discharge
(needs Cayley–Bacharach).

## Build

`docker-build.sh Proofs.PascalsHexagonOQ03` — see PR for status. Entry stays
`axiomatized` via the parent `conic_implies_pascal_constraint` (used only by
`pascalR_on_pascalProjLine`; the PART 4k lemmas themselves are axiom-free).
