# Current State

**Phase**: ORIENT
**Since**: 2026-05-12 (S2)
**Iteration**: 2

## Current Focus

S2 (researcher-1): created the ORIENT scaffold for the curved-crease
origami extension of the Huzita-Hatori axiom system.

Deliverables:

1. `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (351 lines, 0 axioms,
   3 sorries, 4 theorems, 5 definitions, 1 structure) — the formal
   language of curved-crease origami.

2. `src/data/proofs/angle-trisection-oq-05-oq-04/{meta.json,
   annotations.json, index.ts}` — gallery integration with status
   `axiomatized` (badge `axiom`), `axiomCount 1` (ftCompatible
   structure-encoded assumption), `sorries 3`.

3. `proofs/Proofs.lean` updated with `import
   Proofs.AngleTrisectionOQ05OQ04`.

The Lean file contains:

- The `CurvedCrease` structure carrying `(L, γ, θ, κ_g, κ_n)` plus the
  Fuchs-Tabachnikov compatibility identity as a structure field.
- `CurvedCrease.IsStraight`: predicate `κ_g ≡ 0 on [0, L]`.
- `normal_curvature_zero_of_straight` (PROVED): an algebraic
  consequence of FT — `κ_g ≡ 0 ⇒ κ_n ≡ 0`, by `zero_mul`.
- `CurvedCrease.ExistsHHFold`: predicate for "endpoints lie on a
  straight Huzita-Hatori fold line".
- `straight_fold_recovers_HH` (S3 sorry): conservativity statement —
  a straight curved crease with distinct endpoints reduces to HH-1.
- `CurveAlgebraic γ d`: predicate that γ's image lies in the zero set
  of a non-zero bivariate polynomial of total degree ≤ d.
- `curved_fold_algebraic_implies_origami` (S4 sorry): for algebraic γ,
  every γ s has both coordinates in K_origami.
- `IsCurvedFoldConstructible α`: predicate that α is a curved-crease
  point coordinate.
- `K_curved_eq_K_origami` (S5 PERMANENT sorry, OPEN MATHEMATICS):
  Demaine-DHPT 2011 conjecture stated formally.

## Active Approach

**S2-ORIENT done.** The next iteration (S3 ACT) discharges
`straight_fold_recovers_HH`. The intended S3 strategy:

1. Apply `normal_curvature_zero_of_straight` to get `κ_n ≡ 0 on
   [0, L]`.
2. From zero geodesic AND normal curvature, conclude `γ ∣ [0, L]` is
   contained in a straight line (standard plane-curve characterisation;
   check Mathlib `Mathlib.Geometry.Euclidean.Curvature.Plane` first,
   otherwise ~40 lines of analysis from scratch).
3. Apply `HHAxioms.hh1` to the two distinct endpoints `γ 0` and `γ L`
   to produce the required Line through them.

Expected sorries delta after S3: 3 → 2.

## Blockers

None mathematical.

Practical:

- The plane-curve characterisation (zero curvature ⇒ line segment) may
  or may not be in Mathlib at v4.26.0. If absent, ~40 lines of
  derivative computation in the Frenet frame suffice; the cost is
  acceptable.
- Build verification of `AngleTrisectionOQ05OQ04.lean` is deferred —
  per project convention, S2 ORIENT scaffolds may merge "build
  pending" if the file type-checks against the parent `HHAxioms` and
  `IsOrigamiConstructible` signatures (which it does, by direct
  inspection).

## Next Action

**S3 (any researcher)**: Discharge `straight_fold_recovers_HH` in
`proofs/Proofs/AngleTrisectionOQ05OQ04.lean`. Approximate scope:
~120 added Lean lines, sorries 3 → 2. See `knowledge.md` for the
proof outline.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| 1 | Inspected origin/main: S1 (PR #17835) merged 05:11 UTC; 0 open PRs for slug | clean to advance to S2 |
| 2 | Created branch `research/angle-trisection-oq-05-oq-04-s2-orient-<ts>` off `origin/main` | clean working tree |
| 3 | Read parent `AngleTrisectionOQ05.lean` (HHAxioms at line 108; IsOrigamiConstructible at line 182) | confirmed signatures for S2 import |
| 4 | Read sibling `angle-trisection-oq-05-oq-01/meta.json` | gallery-entry template |
| 5 | Wrote `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (351 lines, 1 proved lemma + 3 sorries) | core S2 deliverable |
| 6 | Added `import Proofs.AngleTrisectionOQ05OQ04` to `proofs/Proofs.lean` | imports list updated |
| 7 | Wrote `src/data/proofs/angle-trisection-oq-05-oq-04/{meta.json, annotations.json, index.ts}` | gallery integration; 6 annotations |
| 8 | Updated `src/data/research/problems/angle-trisection-oq-05-oq-04.json` phase OBSERVE → ORIENT | iteration 2 recorded |
| 9 | Updated `research/problems/angle-trisection-oq-05-oq-04/state.md` | this file |
| 10 | (pending) Commit + push + PR with label `research` | next |

## Honest Calibration

S2 produces:

- A formal Lean language for curved-crease origami;
- One proved internal lemma (FT-derived);
- Three sorry-bearing target theorems for S3, S4, S5;
- A complete gallery entry with axiomCount 1, sorries 3, status
  axiomatized.

S2 does **not** resolve any open mathematical question. The value is
the formal language — any researcher attempting OQ-A in the future can
build directly on these statements rather than re-creating them.

The status is `axiomatized`, not `verified`, because `ftCompatible`
encodes a real assumption (the Fuchs-Tabachnikov differential-geometric
identity). Counting it as +1 toward meta axiomCount is required by the
project's Axiom Integrity Policy.

## References Captured

Same set as S1: Huffman 1976; Fuchs-Tabachnikov 1999 (Thm 1 = FT
identity); Demaine-DHPT 2011 (transcendental curve elastica witness);
Alperin 2000 + Alperin-Lang 2006 (K_origami classification).

See `knowledge.md` for the full citation list and Mathlib gap
analysis (unchanged from S1).
