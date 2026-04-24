/-
# Minkowski Fundamental Theorem OQ-04: Custom Lattice API ≃ Module.Basis

## Open Question
Is the custom `Lattice n` structure from MinkowskiFundamentalTheorem.lean equivalent
to Mathlib's canonical `Module.Basis (Fin n) ℝ (Fin n → ℝ)` type?

## Answer: YES — Full Equivalence

The two representations are in canonical bijection:
- `toFun`: `Lattice n → Module.Basis` via `L.toModuleBasis` (rows become basis vectors)
- `invFun`: `Module.Basis → Lattice n` via `latticeOfBasis` (proved here)

**Key lemma**: For any `b : Module.Basis (Fin n) ℝ (Fin n → ℝ)`:
  `(Matrix.of b).det ≠ 0`

**Proof**: Using `(Pi.basisFun ℝ (Fin n)).toMatrix b = (Matrix.of b)ᵀ` and
`b.toMatrix e * e.toMatrix b = 1`, we get:
`det(b.toMatrix e) * det((Matrix.of b)ᵀ) = 1`, so by `det_transpose`:
`det(b.toMatrix e) * det(Matrix.of b) = 1 ≠ 0`.

Note: We work in `Fin n → ℝ` (the standard n-dimensional coordinate space) rather
than `EuclideanSpace ℝ (Fin n)` to avoid PiLp module-instance complications. These
spaces are isomorphic as ℝ-modules so the mathematical content is identical.
-/

import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open Set Module
open scoped Matrix

namespace MinkowskiFundamentalTheoremOQ04

variable (n : ℕ) [NeZero n]

/-- Custom lattice: a basis matrix with nonzero determinant. -/
structure Lattice where
  basis : Matrix (Fin n) (Fin n) ℝ
  basis_invertible : basis.det ≠ 0

-- ============================================================
-- PART 1: Key Lemma — Module.Basis matrix has nonzero det
-- ============================================================

/-- For `e = Pi.basisFun ℝ (Fin n)` (standard basis for `Fin n → ℝ`),
    `e.toMatrix b = (Matrix.of b)ᵀ`.

    Proof: Each entry is `e.repr (b j) i = (b j) i = (Matrix.of b) j i
    = (Matrix.of b)ᵀ i j`. -/
theorem piBasicFun_toMatrix_eq_transpose (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    (Pi.basisFun ℝ (Fin n)).toMatrix b = (Matrix.of b)ᵀ := by
  ext i j
  simp only [Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.transpose_apply, Matrix.of_apply]

/-- **The key lemma**: The matrix `Matrix.of b` has nonzero determinant for any
    `Module.Basis (Fin n) ℝ (Fin n → ℝ)`. This enables constructing `Lattice n` from
    any `Module.Basis`. -/
theorem basis_matrix_det_ne_zero (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    (Matrix.of b).det ≠ 0 := by
  set e := Pi.basisFun ℝ (Fin n) with he_def
  have hprod : b.toMatrix e * e.toMatrix b = 1 :=
    Basis.toMatrix_mul_toMatrix_flip b e
  have hmat : e.toMatrix b = (Matrix.of b)ᵀ := piBasicFun_toMatrix_eq_transpose n b
  have hdet : (b.toMatrix e).det * (Matrix.of b).det = 1 := by
    have h1 := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_one] at h1
    rw [hmat, Matrix.det_transpose] at h1
    exact h1
  intro h0
  simp only [h0, mul_zero] at hdet
  exact one_ne_zero hdet.symm

-- ============================================================
-- PART 2: The Converse Conversion — Module.Basis → Lattice n
-- ============================================================

/-- **Convert any `Module.Basis` to a `Lattice n`**.
    The lattice basis matrix is `Matrix.of b` (rows = basis vectors). -/
noncomputable def latticeOfBasis (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) : Lattice n where
  basis := Matrix.of b
  basis_invertible := basis_matrix_det_ne_zero n b

-- ============================================================
-- PART 3: Conversion Functions — Lattice n → Module.Basis
-- ============================================================

/-- The lattice's linear equivalence via its basis matrix (transpose mult on `Fin n → ℝ`). -/
noncomputable def Lattice.toLinearEquiv (L : Lattice n) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := by
  apply LinearEquiv.ofBijective L.basis.transpose.mulVecLin
  haveI : Invertible L.basis.transpose :=
    Matrix.invertibleOfIsUnitDet _
      (isUnit_iff_ne_zero.mpr (by rw [Matrix.det_transpose]; exact L.basis_invertible))
  constructor
  · intro a b h
    simp only [Matrix.mulVecLin_apply] at h
    exact Matrix.mulVec_injective_of_invertible _ h
  · intro y
    obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_of_invertible L.basis.transpose y
    exact ⟨x, by simp only [Matrix.mulVecLin_apply]; exact hx⟩

/-- Module basis from the lattice's basis matrix. -/
noncomputable def Lattice.toModuleBasis (L : Lattice n) : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map (L.toLinearEquiv n)

/-- The matrix of `L.toModuleBasis` equals `L.basis`. -/
theorem Lattice.toModuleBasis_matrix_eq (L : Lattice n) :
    Matrix.of (L.toModuleBasis n) = L.basis := by
  ext i j
  -- Matrix.of_apply and Basis.map_apply are rfl, so show reduces the goal:
  show (L.toLinearEquiv n (Pi.basisFun ℝ (Fin n) i)) j = L.basis i j
  -- L.toLinearEquiv n is definitionally LinearEquiv.ofBijective mulVecLin _,
  -- which applies as mulVecLin:
  change (L.basis.transpose.mulVecLin (Pi.basisFun ℝ (Fin n) i)) j = L.basis i j
  simp only [Matrix.mulVecLin_apply, Pi.basisFun_apply, Matrix.mulVec_single_one,
             Matrix.col_def, Matrix.transpose_transpose]

-- ============================================================
-- PART 4: Round-Trip Theorems — Proving the Equivalence
-- ============================================================

/-- **Round-trip 1**: `latticeOfBasis (L.toModuleBasis n) = L`. -/
theorem toModuleBasis_latticeOfBasis (L : Lattice n) :
    latticeOfBasis n (L.toModuleBasis n) = L := by
  cases L with
  | mk basis h =>
    simp only [latticeOfBasis, Lattice.mk.injEq]
    exact Lattice.toModuleBasis_matrix_eq n ⟨basis, h⟩

/-- **Round-trip 2**: `(latticeOfBasis n b).toModuleBasis n = b`.

    Proof: Their matrices agree (`toModuleBasis_matrix_eq` + `latticeOfBasis` unfold),
    so their basis vectors agree coordinate-wise. -/
theorem latticeOfBasis_toModuleBasis (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    (latticeOfBasis n b).toModuleBasis n = b := by
  -- Step 1: The matrices of both sides are equal
  have hmat : Matrix.of ((latticeOfBasis n b).toModuleBasis n) = Matrix.of b := by
    have h := (latticeOfBasis n b).toModuleBasis_matrix_eq n
    simp only [latticeOfBasis] at h
    exact h
  -- Step 2: Equal matrices → equal bases (Matrix.of is the identity on Fin n → Fin n → ℝ)
  apply DFunLike.ext
  intro i
  funext j
  exact congrFun (congrFun hmat i) j

-- ============================================================
-- PART 5: The Type Equivalence
-- ============================================================

/-- **Main Theorem**: `Lattice n ≃ Module.Basis (Fin n) ℝ (Fin n → ℝ)`.

    The custom `Lattice n` API and Mathlib's `Module.Basis` API are canonically
    equivalent:
    - Custom API: explicit matrix + invertibility condition, covolume = `|det(L.basis)|`
    - Mathlib API: basis vectors in `Fin n → ℝ`, covolume via fundamental domain volume -/
noncomputable def latticeEquivBasis :
    Lattice n ≃ Module.Basis (Fin n) ℝ (Fin n → ℝ) where
  toFun L := L.toModuleBasis n
  invFun b := latticeOfBasis n b
  left_inv L := toModuleBasis_latticeOfBasis n L
  right_inv b := latticeOfBasis_toModuleBasis n b

end MinkowskiFundamentalTheoremOQ04
