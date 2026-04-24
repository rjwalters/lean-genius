# Knowledge Base: minkowski-fundamental-theorem-oq-04

**Problem**: Is the custom `Lattice n` structure (basis matrix + invertibility) canonically equivalent to Mathlib's `Module.Basis (Fin n) ℝ (Fin n → ℝ)`?

**Answer**: YES. `Lattice n ≃ Module.Basis (Fin n) ℝ (Fin n → ℝ)` — proved and verified.

**Status**: COMPLETED — 0 sorries, 0 axioms, build verified.

---

## Session 2026-04-24 (Session 1) — Complete Proof

**Mode**: FRESH
**Outcome**: completed

### What I Did

- Fixed the original broken proof (wrong theorem direction, non-existent Mathlib lemmas)
- Proved `piBasicFun_toMatrix_eq_transpose`: `(Pi.basisFun ℝ (Fin n)).toMatrix b = (Matrix.of b)ᵀ`
- Proved `basis_matrix_det_ne_zero`: `(Matrix.of b).det ≠ 0` for any `Module.Basis`
- Defined `latticeOfBasis n b : Lattice n` with `basis := Matrix.of b`
- Defined `Lattice.toLinearEquiv` via `L.basis.transpose.mulVecLin` + `Matrix.invertibleOfIsUnitDet`
- Proved `Lattice.toModuleBasis_matrix_eq`: `Matrix.of (L.toModuleBasis n) = L.basis`
- Proved both round-trips and assembled `latticeEquivBasis : Lattice n ≃ Module.Basis (Fin n) ℝ (Fin n → ℝ)`
- Created gallery data: annotations.json (4 annotations), meta.json (verified), index.ts

### Key Findings

- **`open scoped Matrix` required** for `ᵀ` transpose notation (it is `scoped[Matrix]`, not globally available)
- **`open Module` required** for `Basis.*` lemmas — they live in `namespace Module.Basis`, not top-level `Basis`
- **Correct lemma name**: `Basis.toMatrix_mul_toMatrix_flip` (not `toMatrix_mul_toMatrix`). Signature: `b.toMatrix b' * b'.toMatrix b = 1`
- **Key proof step**: `e.toMatrix b = (Matrix.of b)ᵀ` from `Pi.basisFun_repr` + the product formula forces `det(Matrix.of b) ≠ 0`
- **`toModuleBasis_matrix_eq` key**: use `show`/`change` tactics since `Basis.map_apply` is `rfl` (definitional), then `Matrix.mulVec_single_one` extracts the column
- **`Matrix.mulVec_single_one`**: `M *ᵥ Pi.single j 1 = M.col j` — the key simp lemma for the matrix equality proof
- **`Matrix.col_def`**: `M.col j = Mᵀ j` — needed together with `Matrix.transpose_transpose` to close the goal
- **Working in `Fin n → ℝ`** (not `EuclideanSpace ℝ (Fin n)` = `PiLp 2`) avoids typeclass complications

### Files Modified

- `proofs/Proofs/MinkowskiFundamentalTheoremOQ04.lean` (167 lines, complete proof)
- `src/data/proofs/minkowski-fundamental-theorem-oq-04/meta.json` (updated to verified)
- `src/data/proofs/minkowski-fundamental-theorem-oq-04/annotations.json` (created, 4 annotations)
- `src/data/proofs/minkowski-fundamental-theorem-oq-04/index.ts` (created)

### Next Steps

- Follow-up OQ: Prove covolume identity `|det(L.basis)| = vol(ZSpan.fundamentalDomain (L.toModuleBasis n))`
- Follow-up OQ: Establish `instIsZLatticeCustom` — the ZSpan of a custom lattice satisfies `IsZLattice`
