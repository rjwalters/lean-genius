# State: spectral-trace-det-eigenvalues-oq-01-oq-01

**Phase**: COMPLETED (diagonalizable case)
**Lean file**: proofs/Proofs/SpectralTraceDetEigenvaluesOQ01OQ01.lean
**Verification**: host `lake env lean` clean; axioms = {propext, Classical.choice, Quot.sound} only.

## Theorems (12)
- `conj_pow` — (P·M·P⁻¹)ᵏ = P·Mᵏ·P⁻¹
- `charpoly_eq_of_isDiagonalizable` — A.charpoly = ∏ i, (X - d i)
- `eigenvalues_eq_of_isDiagonalizable` — A.charpoly.roots = univ.val.map d
- `trace_pow_eq_sum_diagonal` — trace(Aᵏ) = Σ (d i)ᵏ
- `trace_pow_eq_sum_pow_eigenvalues` — **main**: trace(Aᵏ) = ((eigenvalues A).map (·^k)).sum
- `trace_eq_sum_eigenvalues_of_isDiagonalizable` — k=1 recovers parent
- `isDiagonalizable_diagonal`, `trace_pow_diagonal`
- `diagonal_example`, `Pexample` (def), `example_eq`, `isDiagonalizable_example`, `trace_sq_example`

## Definitions (3)
- `eigenvalues` (abbrev), `IsDiagonalizable`, `Pexample`

## Open (deferred)
- Unconditional alg-closed case (needs triangularization / spectral mapping w/ multiplicity).
