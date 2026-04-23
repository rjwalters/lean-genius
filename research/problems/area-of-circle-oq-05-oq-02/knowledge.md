# Knowledge: area-of-circle-oq-05-oq-02

## Key Facts

### Mathematical Setup
- Positive-definite real symmetric A: all eigenvalues λᵢ > 0
- ∫_{ℝⁿ} e^{-xᵀAx} dx = √(πⁿ/det A)
- Proof chain: spectral decomposition → change of variables → Fubini → scalar integral

### Scalar Case (from parent)
- ∫_{ℝ} e^{-ax²} dx = √(π/a) for a > 0
- This is the building block for the multivariate case via Fubini

### Spectral Theorem (confirmed in Mathlib)
- `Matrix.IsHermitian.spectral_theorem`: A = conjStarAlgAut 𝕜 _ hH.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hH.eigenvalues))
- `hH.eigenvectorUnitary`: element of `Matrix.unitaryGroup (Fin n) ℝ`
- `Matrix.PosDef.eigenvalues_pos`: hA.isHermitian.eigenvalues i > 0 for all i
- `IsHermitian.det_eq_prod_eigenvalues`: det A = ∏ hH.eigenvalues i (via `simpa using hH.det_eq_prod_eigenvalues (𝕜 := ℝ)`)

### Change of Variables
- UT = star (eigenvectorUnitary) = Uᴴ = Uᵀ for real matrices
- `map_matrix_volume_pi_eq_smul_volume_pi` (in `MeasureTheory.Measure.Lebesgue.Basic`):
  `Measure.map (toLin' M) volume = ENNReal.ofReal (|det M|⁻¹) • volume`
  Requires `det M ≠ 0`
- |det UT| = 1 since U is unitary: det U ∈ unitary ℝ → (det U)² = 1 → det U = ±1
- `integral_map`: ∫ y, f y ∂(map φ μ) = ∫ x, f(φ x) ∂μ
  (in `MeasureTheory.Integral.Bochner.Basic`)

### Key API Locations
- `Matrix.PosDef.eigenvalues_pos`: `Mathlib.Analysis.Matrix.PosDef:85`
- `IsHermitian.det_eq_prod_eigenvalues`: `Mathlib.Analysis.Matrix.Spectrum`
- `map_matrix_volume_pi_eq_smul_volume_pi`: `Mathlib.MeasureTheory.Measure.Lebesgue.Basic:397`
- `integral_map`: `Mathlib.MeasureTheory.Integral.Bochner.Basic:1096`
- `Matrix.det_of_mem_unitary`: `Mathlib.LinearAlgebra.UnitaryGroup:80`
- `Unitary.mem_iff`: `Mathlib.Algebra.Star.Unitary:57`
- `Matrix.star_eq_conjTranspose`: `Mathlib.LinearAlgebra.Matrix.ConjTranspose:398`
- `Matrix.det_conjTranspose`: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic:347`
- `LinearMap.continuous_on_pi`: `Mathlib.Topology.Algebra.Module.Basic:255`
- `integral_fintype_prod_volume_eq_prod`: `Mathlib.MeasureTheory.Integral.Pi`

### Import Chain Note
- `Matrix.star_eq_conjTranspose` and `Matrix.det_conjTranspose` are transitively available via:
  `Analysis.Matrix.Spectrum → LinearAlgebra.Matrix.Rank → LinearAlgebra.Matrix.NonsingularInverse → LinearAlgebra.Matrix.Adjugate → LinearAlgebra.Matrix.MvPolynomial → LinearAlgebra.Matrix.Determinant.Basic → LinearAlgebra.Matrix.RowCol → LinearAlgebra.Matrix.ConjTranspose`
- No extra imports needed beyond those already in the file

### Remaining Sorry: `hquad` (HARD)
The quadratic form rewrite:
```lean
have hquad : ∀ x : Fin n → ℝ,
    dotProduct x (A.mulVec x) = ∑ i : Fin n, hH.eigenvalues i * (UT *ᵥ x) i ^ 2 := by
  intro x
  -- Need: A = U * diag(λ) * Uᵀ from spectral_theorem
  -- Then: xᵀAx = xᵀ(U diag(λ) Uᵀ)x = (Uᵀx)ᵀ diag(λ) (Uᵀx) = ∑ λᵢ (Uᵀx)ᵢ²
  sorry
```
Key steps needed:
1. `hH.spectral_theorem`: A = U * diag(RCLike.ofReal ∘ λ) * star U (conjStarAlgAut form)
2. `dotProduct_mulVec`: x ⬝ᵥ (A *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ x
3. `mulVec_diagonal`: (diagonal v) *ᵥ w = fun i => v i * w i

## Open Questions
- Can `hquad` be proved with `simp [hH.spectral_theorem, ...]` + `dotProduct_mulVec + mulVec_diagonal`?
- Is there a higher-level lemma `IsHermitian.inner_mulVec_eq_sum_eigenvalues_sq`?

## References
- Parent proof: `proofs/Proofs/AreaOfCircleOQ05.lean`
- `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Mathlib.MeasureTheory.Integral.Bochner`
- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`
- `Mathlib.Analysis.Matrix.Spectrum`

---

## Session 2026-04-23 (Session 1) — Full Proof Skeleton Implemented

**Mode**: FRESH
**Outcome**: PROGRESS — 1 sorry (down from full sorry on entire theorem)

### What I Did

1. Read AreaOfCircleOQ05OQ02.lean — understood existing structure
2. Researched Mathlib API for spectral theorem, measure-preserving change of variables
3. Implemented complete proof skeleton for `multivariate_gaussian_integral`:
   - Step 1: eigenvalues positive (`Matrix.PosDef.eigenvalues_pos`)
   - Step 2: det A = ∏ eigenvalues (`IsHermitian.det_eq_prod_eigenvalues`)
   - Step 3: define UT = star U (conjugate transpose of eigenvector unitary)
   - Step 4: `hquad` (1 sorry — HARD)
   - Step 5: `simp_rw [hquad]` rewrites integrand
   - Step 6: |det UT| = 1 (fully proved via unitary group membership)
   - Step 7: measure-preserving map (`map_matrix_volume_pi_eq_smul_volume_pi`)
   - Step 8: change of variables (`integral_map`)
   - Step 9: apply `diagonal_gaussian` + connect to det via eigenvalues

### Key Findings

**|det UT| = 1 proof chain**:
`Matrix.det_of_mem_unitary` → `Unitary.mem_iff` → `star_trivial` → `(det U)^2 = 1` → `nlinarith` for `(det U - 1)(det U + 1) = 0` → `|det U| = 1`

**Measure-preserving**: `map_matrix_volume_pi_eq_smul_volume_pi hUT_det_ne` gives
`map (toLin' UT) volume = |det UT|⁻¹ • volume = 1 • volume = volume`

**Change of variables**: `integral_map hφ hfm` gives
`∫ y, f y ∂(map φ μ) = ∫ x, f(φ x) ∂μ`

**`hquad` remaining sorry** (HARD): Requires unfolding `IsHermitian.spectral_theorem` form
`A = conjStarAlgAut 𝕜 _ eigenvectorUnitary (diagonal (RCLike.ofReal ∘ eigenvalues))`
into `U * diag(λ) * star U`, then applying `dotProduct_mulVec` and `mulVec_diagonal`.

### Files Modified

- `proofs/Proofs/AreaOfCircleOQ05OQ02.lean` (full proof structure, 1 sorry remaining)
- `research/problems/area-of-circle-oq-05-oq-02/knowledge.md`

### Next Steps

1. Submit `hquad` sorry to Aristotle (HARD — known proof exists via spectral algebra)
2. If Aristotle proves it, 0 sorries → update status to `verified`/`formalized`
3. Alternative manual approach: unfold `conjStarAlgAut_apply` step by step

---

## Session 2026-04-23 (Session 2) — Build Verified, hquad Submitted to Aristotle

**Mode**: REVISIT
**Outcome**: PROGRESS — proof structure build-verified, 1 sorry (hquad) pending Aristotle

### What I Did

1. Fixed parse error from previous session: `hλ_pos` → `heig_pos` (two occurrences)
   - Root cause: `λ` (U+03BB) is still a Lean 4 keyword in v4.26.0, tokenizer splits `hλ_pos` into `h` + keyword `λ` + `_pos`
   - Fix applied at lines 124 and 125 of `AreaOfCircleOQ05OQ02.lean`
2. Verified build: `[3154/3154] Replayed Proofs.AreaOfCircleOQ05OQ02`
   - Only 1 sorry warning at line 116 (hquad) — all other proof steps check correctly
3. Submitted `hquad` sorry to Aristotle for overnight proof search

### Key Findings

**Build succeeds with 1 sorry**: The proof structure is type-correct. All steps outside `hquad` are fully elaborated.
- `hdet`: det A = ∏ eigenvalues via `simpa using hH.det_eq_prod_eigenvalues (𝕜 := ℝ)` ✓
- `habs`: |det UT| = 1 via unitary group → (det U)^2 = 1 → det U = ±1 ✓
- `hmap`: measure-preserving via `map_matrix_volume_pi_eq_smul_volume_pi` ✓
- `hcov`: change of variables via `integral_map` ✓
- Final `rw [hcov, diagonal_gaussian hH.eigenvalues heig_pos, ← hdet]` ✓

**hquad sorry classification**: HARD (not OPEN — proof exists via spectral algebra)
- Needs: `hH.spectral_theorem` in `conjStarAlgAut` form → unfold to U * diag(λ) * star U
- Then: `dotProduct_mulVec`, `mulVec_mulVec`, `mulVec_diagonal`, `dotProduct_comm`

### Files Modified

- `proofs/Proofs/AreaOfCircleOQ05OQ02.lean` (heig_pos fix; confirmed build-verified)
- `src/data/research/problems/area-of-circle-oq-05-oq-02.json` (phase → ACT, knowledge updated)
- `research/problems/area-of-circle-oq-05-oq-02/knowledge.md`

### Next Steps

1. When Aristotle returns hquad proof: integrate into file, rebuild, update sorryCount to 0
2. Update JSON status to `verified` and leanFiles sorryCount to 0
