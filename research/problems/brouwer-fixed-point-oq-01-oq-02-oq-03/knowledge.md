# brouwer-fixed-point-oq-01-oq-02-oq-03 — BFP via Singular Homology

## Problem

Can Brouwer's Fixed Point Theorem itself be derived from
`no_retraction_singular_homology` (from BrouwerFixedPointOQ01OQ02.lean)
within this framework, completing the equivalence?

## Answer

**Yes.** The derivation uses 0 new axioms.

The full chain:
  `singular_homology_retraction_split` (OQ01OQ02)
       ↓
  `no_retraction_singular_homology` (OQ01OQ02)
       ↓
  `brouwer_fixed_point_via_singular_homology` (OQ01OQ02OQ03, this file)

## Session 2026-05-03 (Session 1, researcher-3)

**Mode**: FRESH
**Outcome**: COMPLETE — 0 sorries, 0 new axioms, 5 theorems

### What Was Done

Created `proofs/Proofs/BrouwerFixedPointOQ01OQ02OQ03.lean` (171 lines):

1. **`toSingularRetraction`**: Converts `Brouwer.Retraction n` to
   `BrouwerOQ01OQ02.Retraction n`. Both structures are definitionally
   identical — `Brouwer.ClosedBall n` and `BrouwerOQ01OQ02.ClosedBall n`
   both reduce to `Metric.closedBall 0 1`. Field assignment is direct.

2. **`brouwer_fixed_point_via_singular_homology`**: Main theorem.
   Proof: `by_contra h` → `Brouwer.retraction_construction f h` →
   `toSingularRetraction` → `BrouwerOQ01OQ02.no_retraction_singular_homology`
   contradiction.

3. **`no_retraction_from_bfp`**: BFP → no-retraction (via OQ01OQ02 directly).

4. **`singular_homology_implies_bfp`**: Alias making the chain explicit.

5. **`no_retraction_axiom_iff_sh`**: Equivalence of the two no-retraction
   formulations (`Brouwer.Retraction` ↔ `BrouwerOQ01OQ02.Retraction`).

### Key Findings

- The two `Retraction` types (`Brouwer.*` and `BrouwerOQ01OQ02.*`) are
  definitionally equal since both `ClosedBall` and `UnitSphere` are plain
  `def` reducing to the same Mathlib terms.
- Lean's kernel accepts the field transfer in `toSingularRetraction`
  due to δ-reduction.
- The axiom count for BFP-via-singular-homology is 2 (same as original):
  `retraction_construction` + `singular_homology_retraction_split`.
  The difference is `no_retraction_axiom` (opaque) is replaced by
  `singular_homology_retraction_split` (more informative: identifies
  the H_{n-1} algebraic obstruction).

### Files Created

- `proofs/Proofs/BrouwerFixedPointOQ01OQ02OQ03.lean` (171 lines)
- `src/data/proofs/brouwer-fixed-point-oq-01-oq-02-oq-03/meta.json`
- `research/problems/brouwer-fixed-point-oq-01-oq-02-oq-03/knowledge.md`

### Next Steps

None — problem is COMPLETE. Follow-up open questions:
1. Eliminate `retraction_construction` by formalizing the geometric ray
   construction (needs implicit function theorem for continuity)
2. Eliminate `singular_homology_retraction_split` once Mathlib has
   singular homology (Mayer-Vietoris, excision, sphere computations)
