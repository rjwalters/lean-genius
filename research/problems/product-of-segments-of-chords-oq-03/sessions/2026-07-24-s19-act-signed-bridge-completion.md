# S19 ACT — Signed chord-product bridge; problem COMPLETE (researcher-2, 2026-07-24)

## What shipped

`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` 542 → 617 LOC, still
**0 sorries / 0 axioms**, docker GREEN (8577 jobs, 2026-07-24; the only
warnings are pre-existing `EuclideanSpace.norm_single` deprecations in the
Converse file).

New Part 13:

- `signed_product_implies_concyclicityDet_zero` — the OQ-03 **bridge claim**:
  chords `AB`, `CD` through `P` (collinearity scalars `t`, `s`), distinct
  chord lines (`LinearIndependent ℝ ![A−P, C−P]`), equal **signed** products
  `⟪A−P, B−P⟫ = ⟪C−P, D−P⟫` ⟹ `concyclicityDet A B C D = 0`.
- `signed_product_implies_concyclic_via_det` — end-to-end round trip:
  signed power-of-a-point ⟹ Δ = 0 ⟹ explicit circumcircle via the Part 12
  iff (adds `¬ Collinear ℝ {A, B, C}`).

## The key discovery: S20 was already done

The plan's S20 ("discharge `converse_product_implies_concyclic_axiom` in the
parent, flip gallery meta axiomatized → verified") is **moot**: the OQ-02
line of work already removed the axiom outright (its unsigned statement is
FALSE — machine-checked `unsigned_converse_counterexample`), proved the
corrected signed converse (`signed_converse_implies_concyclic`,
`Proofs/ProductOfSegmentsOfChordsConverse.lean`, 0 sorries / 0 axioms,
auto-discovered by the lake globs so it IS in the build), and the parent
gallery meta is already `verified` / `original` / `axiomCount 0`
(PR #24873). The parent file has 0 `axiom` declarations.

Consequently S19 did NOT need the S12-§3.2 closed-form
`linear_combination` polynomial witness. The bridge composes three merged
results (Part 6 scalar bridge → Converse-file circumcircle → Part 8
unconditional (⟸) direction) in ~20 lines. The heavy polynomial route is
obsolete — do not resurrect it.

## Deliverable ledger (problem.md "Our Goal" 1–4)

1. `concyclicityDet` definition — ✓ S2 (Parts 1–2).
2. Δ = 0 ⟺ concyclic (non-collinear P₁P₂P₃) — ✓ S18 (Part 12).
3. Chord-product ⟹ Δ = 0 bridge (signed form; unsigned is false) — ✓ **S19
   (Part 13, this session)**.
4. Parent axiom discharged, parent verified — ✓ OQ-02 line (Converse file);
   determinant route now also yields it (`signed_product_implies_concyclic_via_det`).

**Problem COMPLETE.** Adversarial checklist + "Must prove exactly" sections
added to problem.md (element 5/6) per the SOLVED protocol.

## Lean notes

- `hindep.ne_zero 0 : ![u, v] 0 ≠ 0` + `simpa` extracts componentwise
  nonvanishing from `LinearIndependent ℝ ![u, v]`; `sub_ne_zero.mp` then
  gives `A ≠ P`. No `Matrix.cons_val_*` spelling needed.
- Cross-namespace composition (`ProductOfSegmentsOfChordsConverse.Vec2` vs
  local `Vec2`) is frictionless — both are the same
  `abbrev … := EuclideanSpace ℝ (Fin 2)`, so terms unify definitionally.
- Importing `Proofs.ProductOfSegmentsOfChordsConverse` (which imports full
  `Mathlib`) on top of the file's targeted imports is harmless; build stays
  fast because everything is cached.

## Follow-up questions (quality-filtered)

One proposed (depth check: slug has one `-oq-` segment, depth 1 < cap 3):

- **Five-point conic criterion.** Möbius's general determinant: five planar
  points lie on a common conic iff the 5×6 Veronese matrix
  `[x², xy, y², x, y, 1]` has rank ≤ 5 (6-point 6×6 determinant vanishes
  for coconic sextuples). The concyclicity determinant is the specialization
  fixing the conic class to circles. Equivalent-strength note: **strictly
  more general** than this problem's headline (specialization recovers it),
  requiring materially new machinery (rank conditions / general conic
  forms), so it is a genuine new direction, not an equivalent restatement.

No second follow-up — remaining candidates (Ptolemy re-derivation from Δ,
Delaunay in-circle predicate) are shallow specializations or duplicate
existing gallery entries.
