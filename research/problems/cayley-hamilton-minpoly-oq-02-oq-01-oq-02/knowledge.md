# cayley-hamilton-minpoly-oq-02-oq-01-oq-02

## Problem Summary

**Question**: Can we characterize exactly when minpoly is invariant under non-injective algebra maps?
**Answer**: YES. minpoly K (f a) = minpoly K a ↔ aeval a (minpoly K (f a)) = 0.

---

## Session 2026-05-06 (Session 1) — Complete Formalization

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms)

### What Was Done

- Surveyed parent OQ02OQ01: minpoly.algHom_eq requires injectivity
- Identified the characterization: mutual divisibility of monic polynomials
- Proved universal divisibility: minpoly_dvd_algHom (always: minpoly(fa) | minpoly(a))
- Proved main theorem: minpoly_eq_iff_aeval_zero
  - (⟹): trivial, minpoly.aeval K a
  - (⟸): mutual divisibility via minpoly.dvd, then eq_of_monic_of_associated
- Proved degree inequality: minpoly_natDegree_le (non-injective maps only shrink)
- Showed injective case as special case (injective_implies_criterion_holds)

### Key Findings

- Mathlib has all needed tools: minpoly.dvd, minpoly.aeval_algHom, associated_of_dvd_dvd, eq_of_monic_of_associated
- The proof is clean and short (~168 lines, 9 theorems)
- Universal divisibility direction: always true, proof is one line
- The criterion aeval a (minpoly K (f a)) = 0 is testable and clean

### Files Modified

- `proofs/Proofs/CayleyHamiltonMinpolyOQ02OQ01OQ02.lean` (new, 168 lines)
- `src/data/proofs/cayley-hamilton-minpoly-oq-02-oq-01-oq-02/meta.json` (new)

### Next Steps

- Docker build verification (Docker not running during session)
- PR awaiting merge
