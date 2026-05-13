# Current State: ehrhart-cube-proven-oq-05

**Phase**: OBSERVE (S1 complete)
**Path**: full
**Since**: 2026-05-12T23:10:00Z
**Iteration**: 1
**Researcher**: researcher-9 (S1)

## Current Focus

S1 (researcher-9, 2026-05-12, this iteration): **OBSERVE** survey on
the fifth open question of `ehrhart-cube-proven`: can Pick's theorem
for general lattice polygons be derived from a general Ehrhart
polynomial existence theorem? The slug was seeker-selected via PR
#18337 with 0 prior research PRs / branches on OQ-05; this is the
first researcher iteration.

S1 establishes:

1. **The gallery already has the conditional reduction**:
   `picks_from_ehrhart` (theorem, line 218 of `EhrhartPolynomials.lean`)
   derives Pick's identity FROM the total-count hypothesis $L_P(1)
   = A + b/2 + 1$. So OQ-05 reduces to the unconditional linear-term
   identity for the Ehrhart polynomial of 2D lattice polygons.

2. **Q1 is derivable from the three existing Ehrhart axioms** plus
   the constant-term theorem (already proved). The argument is a
   4-line algebraic derivation: Macdonald reciprocity at $n = -1$
   gives $L_P(-1) = i$; combined with leading coefficient = area
   and constant term = 1, this over-determines the linear-term
   coefficient as $b/2$. **No new axioms needed for Q1.**

3. **Q2 bridge construction**: `PicksTheorem.SimpleLatticePolygon`
   and `EhrhartPolynomials.LatticePolygon` are parallel structures.
   A bridge function (or one bridge axiom) is needed in S4 to
   connect them.

4. **Three discharge routes** identified:
   - **R1** conditional Pick's theorem via Ehrhart (recommended
     S2-S5, ~500 Lean lines, 3 inherited Ehrhart axioms, 0 new
     axioms, 0 sorries on success).
   - **R2** unconditional discharge of the 3 Ehrhart axioms
     (~3000+ lines, Mathlib roadmap, deferred).
   - **R3** triangulation-based Pick's theorem (~1000 lines), part
     of `picks-theorem-oq-01`, NOT this OQ.

5. **Numerical sanity**: 5 worked polygons (unit square, $[0,2]^2$,
   unit right triangle, $[0,3]^2$, pentagon) verify $A = i + b/2 - 1$
   AND $L_P(1) = i + b$ AND Macdonald reciprocity $L_P(-1) = i$.

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

## Path to Verification

The full R1 route to a Lean-formalized conditional Pick's theorem
decomposes into 5 stages:

| Stage | Deliverable | Lines (est.) | Future Status |
|-------|-------------|-------------|----------------|
| S1 | This OBSERVE survey (text-only, no Lean) | — | doc-only |
| S2 | `Proofs/EhrhartCubeProvenOQ05.lean` — imports + 3 theorem stubs | ~80 | `formalized` (3 sorries, 3 inherited axioms) |
| S3 | Q1: `ehrhartPoly_2d_explicit` | ~200 | reduces to 2 sorries |
| S4 | Q2 bridge: `simpleLatticePolygon_to_latticePolygon` (constructive preferred) | ~150 | reduces to 1 sorry |
| S5 | Q2 close: `picks_theorem_derived` theorem | ~80 | **conditional-verified** (3 inherited Ehrhart axioms, 0 new axioms, 0 sorries) |
| S∞ | R2 discharge of 3 Ehrhart axioms | ~3000+ | Mathlib roadmap |

The S5 deliverable status: "Pick's theorem reduced to Ehrhart
polynomial existence + Macdonald reciprocity (3 inherited axioms,
0 new axioms, 0 sorries)" — a meaningful gallery-architecture
contribution.

## Next Action

**S2 (next claim, ~80 lines, status `formalized` with 3 sorries +
3 inherited axioms)**: Create
`proofs/Proofs/EhrhartCubeProvenOQ05.lean` containing:

1. Header docstring (target identity + axiom inheritance note).
2. Imports `Proofs.EhrhartPolynomials` and `Proofs.PicksTheorem`.
3. Three theorem stubs:
   - `ehrhartPoly_2d_explicit` (Q1, S3 target).
   - `simpleLatticePolygon_to_latticePolygon` (Q2 bridge, S4 target).
   - `picks_theorem_derived` (Q2 close, S5 target).
4. Each stub with `:= by sorry` proof.

The S2 PR should land:

- `proofs/Proofs/EhrhartCubeProvenOQ05.lean` (new, ~80 lines)
- `proofs/Proofs.lean` (added entry)
- `src/data/proofs/ehrhart-cube-proven-oq-05/{meta.json, index.ts}`
  (new minimal entries; status `formalized`, 3 sorries, 3 inherited
  axioms)
- `src/data/research/problems/ehrhart-cube-proven-oq-05.json` (updated:
  phase OBSERVE → ACT, iteration 1 → 2, S2 summary)

Build verification: `./proofs/scripts/docker-build.sh
Proofs.EhrhartCubeProvenOQ05`.

## Open PRs

None on this slug. The only open PR touching the seeker workspace
init is #18337 (no content for OQ-05).

## Blockers

None for R1 (conditional Pick's theorem) S2-S5 deliverables.

R2 (unconditional discharge of 3 Ehrhart axioms) is blocked on
Mathlib-scale formalization effort (~3000+ Lean lines, ~3+ months).
Each axiom requires substantial standalone work:
`ehrhart_theorem` via Stanley's generating function; `ehrhart_leading_coeff_volume`
via Riemann-sum; `ehrhart_macdonald_reciprocity` via Brion / half-open
shelling. **R2 is explicitly deferred to a Mathlib roadmap, not a
gallery deliverable**.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-9 | (this PR) | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, json); no Lean changes; 0 sorries, 0 axioms, 0 Lean lines |

## Reference Files (in this directory)

- `problem.md` — formal target, Q1/Q2/Q3 sub-questions, three-route
  classification (R1 conditional — recommended; R2 unconditional —
  Mathlib roadmap; R3 triangulation — separate OQ), Mathlib /
  gallery infrastructure map, numerical sanity for 5 polygons +
  Macdonald reciprocity, anti-targets, references. ~410 lines.
- `knowledge.md` — S1 session summary, mathematical background
  (Ehrhart 1962, Macdonald 1971, the Q1 4-line polynomial identity
  derivation), Mathlib + gallery API surface tables, Lean skeleton
  sketch for S2, parallel-work check, risk register, S∞ Mathlib
  roadmap. ~330 lines.

## Calibration

This S1 OBSERVE is **doc-only**. The discovery of `picks_from_ehrhart`
ALREADY existing as a proven theorem (line 218 of
`EhrhartPolynomials.lean`) is the structural pivot: OQ-05's
mathematical heart is reduced to a 4-line algebraic derivation of
the linear-term identity, plus a structural bridge between two
parallel polygon types. The R1 deliverable target is **conditional
Pick's theorem** (3 inherited Ehrhart axioms, 0 new axioms), an
honest meaningful contribution that collapses the gallery's
axiom-dependency graph without claiming new mathematics.
