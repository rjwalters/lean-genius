# Knowledge: spectral-trace-det-eigenvalues-oq-01-oq-01

## Summary

**Status**: COMPLETED (verified, 0 axioms, 0 sorries) — diagonalizable case.

trace(Aᵏ) = Σ λᵢᵏ proved for diagonalizable matrices `A = P · diagonal d · P⁻¹`.
The eigenvalue multiset (charpoly roots) is identified with the diagonal entries via
similarity-invariance of the characteristic polynomial, so the diagonal sum is
genuinely the power sum of the spectrum. k = 1 recovers the parent's trace = Σλ.

## Session 2026-06-24 (Session 1) — FRESH

**Mode**: FRESH
**Outcome**: completed (diagonalizable scope)

### What I Did
- Surveyed Mathlib for the spectral-mapping-with-multiplicity infrastructure needed
  for the unconditional statement. Found NO usable matrix triangularization
  `A = P·T·P⁻¹` (only the endomorphism-level generalized-eigenspace decomposition in
  `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`, plus set-level CFC spectral
  mapping with no multiplicity). General case ⇒ heavy infra (est. 300–800 lines),
  out of one-session scope.
- Scoped to the diagonalizable case, which is fully elementary and Mathlib-supported.
- Wrote `proofs/Proofs/SpectralTraceDetEigenvaluesOQ01OQ01.lean` (178 lines, 12 thms,
  3 defs). Compiles clean on host `lake env lean`; `#print axioms` shows only
  propext/Classical.choice/Quot.sound.

### Key Findings
- `conj_pow`: (P·M·P⁻¹)ᵏ = P·Mᵏ·P⁻¹ by induction (P⁻¹·P = 1 telescoping). Reusable.
- Eigenvalues of a diagonalizable matrix = diagonal entries, via
  `Matrix.charpoly_units_conj` + `Matrix.charpoly_diagonal` +
  `Polynomial.roots_multiset_prod_X_sub_C`.
- trace(Aᵏ) reduction: conj_pow → `Matrix.trace_units_conj` → `Matrix.diagonal_pow`
  → `Matrix.trace_diagonal`.
- Concrete non-diagonal example: symmetric `!![1,2;2,1]` over ℚ diagonalized by
  `!![1,1;1,-1]` (eigenvalues 3, -1); trace(A²) = 10 = 3² + (-1)².

### Files Modified
- proofs/Proofs/SpectralTraceDetEigenvaluesOQ01OQ01.lean (new)
- proofs/Proofs.lean (import)
- src/data/proofs/spectral-trace-det-eigenvalues-oq-01-oq-01/meta.json (new)

### Mathlib Gaps
- No matrix triangularization `A = P·T·P⁻¹` (T upper triangular) over a field where
  charpoly splits; no spectral-mapping theorem with multiplicity for charpoly roots.
  These block the unconditional trace(Aᵏ) = Σλᵏ.

### Next Steps
- Unconditional case: build matrix triangularization from the genEigenspace
  decomposition, then `(Aᵏ).charpoly.roots = (A.charpoly.roots).map (·^k)`.
- Newton recurrence pₖ = e₁pₖ₋₁ − e₂pₖ₋₂ + ⋯ linking traces of powers to the
  parent's charpoly coefficients (Faddeev–LeVerrier).
