# Generalized Riemann Hypothesis for Dirichlet L-functions

## Problem Summary

**Tier**: A | **Significance**: 7 | **Tractability**: 6
**Status**: axiomatized (GRH is open)
**Lean file**: `proofs/Proofs/DirichletsTheoremOQ02OQ01.lean`

The GRH asserts that all non-trivial zeros of Dirichlet L-functions L(s, χ) lie
on the critical line Re(s) = 1/2. This is one of the most important open problems
in mathematics.

## Session 2026-03-25 (Session 1) - GRH Formalization

**Mode**: FRESH
**Outcome**: progress (axiomatized formalization created)

### What I Did
- Assessed tractability of 17 available problems; selected dirichlets-theorem-oq-02 (Tier A, significance 7)
- Read existing infrastructure: DirichletsTheorem.lean (314 lines, 10 theorems) and DirichletsTheoremOQ01.lean (706 lines, 31 theorems, Siegel zeros)
- Read RiemannHypothesis.lean to understand existing GeneralizedRiemannHypothesis definition
- Created DirichletsTheoremOQ02OQ01.lean: 430 lines, 15 theorems proved, 13 axioms, 1 sorry
- Created gallery entry in src/data/proofs/dirichlets-theorem-oq-02-oq-01/

### Key Findings
- GRH ↔ GRH_right_half: the functional equation maps zeros at s to 1-s, so "no zeros with Re > 1/2" is equivalent to "all zeros on Re = 1/2"
- GRH immediately eliminates Siegel zeros (connecting to OQ01): any β ∈ (1-c/log q, 1) has β > 1/2
- GRH gives EFFECTIVE L(1,χ) bound C/(log q)² vs Siegel's INEFFECTIVE C(ε)/q^ε
- Under GRH, Linnik bound improves from O(q^5) to O(q² log² q) — proved q²(log q)² < q^5

### Files Created/Modified
- `proofs/Proofs/DirichletsTheoremOQ02OQ01.lean` (NEW, 430 lines)
- `src/data/proofs/dirichlets-theorem-oq-02-oq-01/meta.json` (NEW)
- `src/data/proofs/dirichlets-theorem-oq-02-oq-01/index.ts` (NEW)
- `src/data/proofs/dirichlets-theorem-oq-02-oq-01/annotations.json` (NEW)
- `src/data/proofs/dirichlets-theorem-oq-02-oq-01/tacticStates.json` (NEW)

### Remaining Sorry
1. `GRH_error_sublinear`: log x < √x for x > e⁴ (real analysis bound, not mathematically deep)

### Next Steps
- Try to prove the remaining sorry (submit to Aristotle if manual attempt fails)
- Consider connecting to RiemannHypothesis.lean's GeneralizedRiemannHypothesis via an equivalence theorem
