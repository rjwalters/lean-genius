# Green's Theorem OQ-03: Knowledge

## Summary

**Status**: COMPLETED
**Lean file**: `proofs/Proofs/GreensTheoremOQ03.lean`
**Stats**: 31 theorems, 3 axioms, 0 sorries
**PR**: #3325

## Problem

Replace the abstract `GreenRegion` (with `dummy : Unit`) with a concrete
simply-connected region structure and state meaningful Green's theorem.

## Solution

Built TypeI (vertically simple) and TypeII (horizontally simple) region
structures. Proved the two inner FTC halves that form the computational
core of the standard Green's theorem proof (Apostol §17.4).

## Session 2026-02-27 (Session 2) - TypeII, Inner FTC, Disk Geometry

**Mode**: FRESH (continuation)
**Outcome**: completed

### What I Did
- Added TypeII (horizontally simple) region structure with membership, area, iterated integral
- Proved Inner FTC for TypeI (P contribution): `typeI_inner_ftc_P`
- Proved Inner FTC for TypeII (Q contribution): `typeII_inner_ftc_Q`
- Proved P boundary sign relationship: `typeI_P_boundary`
- Added disk as TypeI + TypeII with membership characterization: `disk_mem_iff`
- Proved semicircle area from disk area (eliminated one axiom): `upper_semicircle_area`
- Added rectangle TypeI-TypeII set equality
- Fixed AreaOfCircleOQ01OQ03 (pi_lt_four, tan/cos proof, equilateral triangle)
- Added `open Real` to fix π notation scoping

### Key Findings
- `integral_congr` + `integral_eq_sub_of_hasDerivAt` is the core pattern for inner FTC
- `intervalIntegral.integral_smul` pulls constants out of interval integrals
- `π` notation requires `open Real` (or `open scoped Real`); without it, `π` gets auto-bound as an implicit variable in axioms
- `sq_le_sq'` converts `-√a ≤ y ≤ √a` to `y² ≤ a` for disk membership
- Full rectangle Green's theorem from TypeI+TypeII requires Fubini for variable limits, which has messy integrability conditions

### Files Modified
- `proofs/Proofs/GreensTheoremOQ03.lean` (265 lines added)
- `proofs/Proofs/AreaOfCircleOQ01OQ03.lean` (109 line changes)
- `src/data/proofs/greens-theorem-oq-03/meta.json` (updated)

### Remaining Axioms
1. `greens_theorem_typeI` - full statement combining P+Q; needs Fubini for variable limits
2. `disk_area_eq_pi` - needs arcsine integral antiderivative
3. (upper_semicircle_area was ELIMINATED - proved from disk_area_eq_pi)

### Next Steps
- Prove `disk_area_eq_pi` via antiderivative F(x) = (x√(r²-x²) + r²·arcsin(x/r))/2
- Consider proving Fubini for rectangles to combine both FTCs into full Green's theorem
