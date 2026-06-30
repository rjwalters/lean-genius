/-
  Determinant of the conjugate transpose: `det Mᴴ = star (det M)`.

  Over a `StarRing R` — canonically `R = ℂ` with `star` the complex conjugate —
  taking the conjugate transpose of a square matrix conjugates its determinant:

      det Mᴴ = star (det M).

  This base identity is `Matrix.det_conjTranspose`; the gallery had no entry on
  it (it is distinct from `det_mul` / `det_transpose`).  The substantive content
  here is the pair of structural corollaries it powers, which tie the
  adjoint/spectral structure of complex matrices to a single scalar invariant:

    * **Hermitian ⟹ self-adjoint determinant.**  If `Mᴴ = M` then
      `star (det M) = det M`: the determinant is fixed by conjugation.  Over `ℂ`
      this says the determinant of a Hermitian matrix is a *real* number
      (`(det M).im = 0`, equivalently `det M = (r : ℂ)` for some `r : ℝ`) — the
      scalar shadow of the fact that a Hermitian operator has real spectrum.

    * **Unitary ⟹ determinant on the unit circle.**  If `Uᴴ * U = 1` then,
      applying `det` to both sides, `star (det U) * det U = 1`, hence
      `‖det U‖ = 1`: the determinant of a unitary matrix lies on the unit circle.
      This is the `det : U(n) → U(1)` picture in one line.

  Verified: 0 sorries, 0 axioms (only the foundational propext / Classical.choice
  / Quot.sound; no native_decide, no Lean.ofReduceBool).
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

open Matrix

namespace DetConjugateTransposeOQ01

/-! ### The base identity -/

/-- **Determinant of the conjugate transpose**: over a `StarRing R`,
`det Mᴴ = star (det M)`.  This re-exports `Matrix.det_conjTranspose`; the
corollaries below are the original content. -/
theorem det_conjTranspose {R : Type*} [CommRing R] [StarRing R]
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R) :
    (Mᴴ).det = star M.det :=
  Matrix.det_conjTranspose M

/-! ### Hermitian matrices: the determinant is self-adjoint -/

/-- If `M` is Hermitian (`Mᴴ = M`) then its determinant is self-adjoint:
`star (det M) = det M`.  The determinant is fixed by the conjugation `star`. -/
theorem isSelfAdjoint_det_of_isHermitian {R : Type*} [CommRing R] [StarRing R]
    {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n R}
    (hM : M.IsHermitian) : IsSelfAdjoint (det M) := by
  -- `det Mᴴ = star (det M)`, and `Mᴴ = M`, so `det M = star (det M)`.
  have h := Matrix.det_conjTranspose M
  rw [hM.eq] at h
  exact h.symm

/-- Over `ℂ`, the determinant of a Hermitian matrix has zero imaginary part:
`(det M).im = 0`.  (The scalar form of "Hermitian operators have real
spectrum".) -/
theorem isHermitian_det_im_zero {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) : (det M).im = 0 := by
  have h := isSelfAdjoint_det_of_isHermitian hM
  rw [isSelfAdjoint_iff, ← starRingEnd_apply] at h
  exact Complex.conj_eq_iff_im.mp h

/-- Over `ℂ`, the determinant of a Hermitian matrix is real: it equals
`(r : ℂ)` for some real `r`. -/
theorem isHermitian_det_isReal {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) : ∃ r : ℝ, det M = (r : ℂ) := by
  have h := isSelfAdjoint_det_of_isHermitian hM
  rw [isSelfAdjoint_iff, ← starRingEnd_apply] at h
  exact Complex.conj_eq_iff_real.mp h

/-! ### Unitary matrices: the determinant lies on the unit circle -/

/-- If `Uᴴ * U = 1` (i.e. `U` is unitary) then `star (det U) * det U = 1`.
Obtained by applying `det` to the unitarity relation and using `det_mul`,
`det_conjTranspose`, `det_one`. -/
theorem star_det_mul_det_of_unitary {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) : star (det U) * det U = 1 := by
  have h := congrArg det hU
  rwa [det_mul, Matrix.det_conjTranspose, det_one] at h

/-- **Unitary determinant has modulus one**: if `Uᴴ * U = 1` then `‖det U‖ = 1`,
so `det U` lies on the unit circle.  This is `det : U(n) → U(1)`. -/
theorem unitary_det_norm_one {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) : ‖det U‖ = 1 := by
  have hz : star (det U) * det U = 1 := star_det_mul_det_of_unitary hU
  -- Take norms: `‖star z‖ * ‖z‖ = 1`, i.e. `‖z‖² = 1`.
  have hsq : ‖det U‖ * ‖det U‖ = 1 := by
    have h2 := congrArg norm hz
    rwa [norm_mul, norm_star, norm_one] at h2
  -- `(‖z‖ - 1)(‖z‖ + 1) = 0` and `‖z‖ ≥ 0` force `‖z‖ = 1`.
  have hfac : (‖det U‖ - 1) * (‖det U‖ + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith [norm_nonneg (det U)]

/-! ### Worked instances -/

/-- The identity matrix is Hermitian, so its determinant (which is `1`) is real:
`(det 1).im = 0`. -/
example : (det (1 : Matrix (Fin 2) (Fin 2) ℂ)).im = 0 :=
  isHermitian_det_im_zero Matrix.isHermitian_one

/-- The identity matrix is unitary, so its determinant lies on the unit circle:
`‖det 1‖ = 1`. -/
example : ‖det (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 :=
  unitary_det_norm_one (by simp)

end DetConjugateTransposeOQ01
