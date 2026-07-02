/-
  Polar decomposition of a matrix from the positive semidefinite square root.

  This entry answers the first open question of the PSD-square-root entry
  (`matrix-posdef-sqrt-oq-01`): *"Can the polar decomposition `A = U · P` be
  formalised, with `P = √(AᴴA)` positive semidefinite and `U` unitary?"*

  Working over `𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`), we build the **right polar
  factor** `P = √(AᴴA)` from the continuous-functional-calculus square root
  `CFC.sqrt` and package the polar decomposition:

    * **Uniqueness of the PSD factor (no hypothesis on `A`).**  If `A = U · P`
      with `U` unitary and `P` positive semidefinite, then necessarily
      `P = √(AᴴA)`.  This is the structural heart: it follows purely from
      `AᴴA = Pᴴ (UᴴU) P = P²` and the uniqueness of the PSD square root, and it
      needs *no* invertibility of `A`.

    * **Existence (invertible `A`).**  For an invertible matrix `A` the factor
      `P = √(AᴴA)` is itself invertible, and `U := A · P⁻¹` is unitary with
      `A = U · P`.  This is the classical polar decomposition in the regular
      (generic) case, where both factors are honestly recovered.

    * **Full uniqueness (invertible `A`).**  For invertible `A` the pair
      `(U, P)` is unique: any two right polar decompositions coincide.

    * **Left polar decomposition.**  Applying the right decomposition to `Aᴴ`
      and transposing yields `A = P' · U'` with `P' = √(A Aᴴ)` positive
      semidefinite and `U'` unitary — the mirror form.

  The unitary factor is expressed as membership in `unitary (Matrix n n 𝕜)`,
  i.e. `star U * U = 1 ∧ U * star U = 1` with `star` the conjugate transpose.

  Scope note: only the *invertible* case is claimed for existence.  The general
  (possibly singular) square-matrix polar decomposition additionally requires
  extending a partial isometry supported on `range Aᴴ` to a full unitary, which
  is not developed here.  The uniqueness-of-`P` statement, however, is fully
  general.

  Verified: 0 sorries, 0 axioms beyond the foundational `propext` /
  `Classical.choice` / `Quot.sound`; no `native_decide`, no `Lean.ofReduceBool`.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open Matrix
open scoped MatrixOrder ComplexOrder

namespace MatrixPosDefSqrtOQ01OQ01

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The positive semidefinite polar factor `√(AᴴA)` -/

/-- The right polar factor of `A`, the positive semidefinite square root of
`Aᴴ · A`. -/
noncomputable def polarFactor (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  CFC.sqrt (Aᴴ * A)

/-- The polar factor is positive semidefinite. -/
theorem polarFactor_posSemidef (A : Matrix n n 𝕜) : (polarFactor A).PosSemidef :=
  (CFC.sqrt_nonneg (Aᴴ * A)).posSemidef

/-- The defining property of the polar factor: `(√(AᴴA))² = AᴴA`. -/
theorem polarFactor_mul_self (A : Matrix n n 𝕜) :
    polarFactor A * polarFactor A = Aᴴ * A :=
  CFC.sqrt_mul_sqrt_self (Aᴴ * A) (posSemidef_conjTranspose_mul_self A).nonneg

/-! ### Uniqueness of the PSD factor (fully general) -/

/-- **Uniqueness of the positive semidefinite polar factor.**  If `A = U · P`
with `U` unitary and `P` positive semidefinite, then `P` is forced to be the
polar factor `√(AᴴA)`.  No invertibility of `A` is required. -/
theorem polar_psd_unique (A U P : Matrix n n 𝕜)
    (hU : U ∈ unitary (Matrix n n 𝕜)) (hP : P.PosSemidef) (h : A = U * P) :
    P = polarFactor A := by
  have huu : Uᴴ * U = 1 := by
    have := Unitary.star_mul_self_of_mem hU
    rwa [star_eq_conjTranspose] at this
  have hAHA : Aᴴ * A = P * P := by
    subst h
    rw [conjTranspose_mul, hP.isHermitian]
    rw [mul_assoc, ← mul_assoc Uᴴ U P, huu, one_mul]
  exact (CFC.sqrt_unique hAHA.symm hP.nonneg).symm

/-! ### Invertibility of the polar factor for invertible `A` -/

/-- For an invertible matrix `A`, the polar factor `√(AᴴA)` is invertible. -/
theorem polarFactor_isUnit_det (A : Matrix n n 𝕜) (hA : IsUnit A) :
    IsUnit (polarFactor A).det := by
  have hdetA : A.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det A).mp hA)
  have key : (polarFactor A).det * (polarFactor A).det = star A.det * A.det := by
    have h := congrArg det (polarFactor_mul_self A)
    rwa [det_mul, det_mul, det_conjTranspose] at h
  have hRHS : star A.det * A.det ≠ 0 :=
    mul_ne_zero (star_ne_zero.mpr hdetA) hdetA
  have hne : (polarFactor A).det ≠ 0 := by
    intro h
    rw [h, zero_mul] at key
    exact hRHS key.symm
  exact isUnit_iff_ne_zero.mpr hne

/-! ### Existence: the right polar decomposition `A = U · √(AᴴA)` -/

/-- **Right polar decomposition (invertible case).**  Every invertible matrix
`A` factors as `A = U · P` with `U` unitary and `P = √(AᴴA)` positive
semidefinite (and invertible). -/
theorem polar_right (A : Matrix n n 𝕜) (hA : IsUnit A) :
    ∃ U : Matrix n n 𝕜, U ∈ unitary (Matrix n n 𝕜) ∧ A = U * polarFactor A := by
  set P := polarFactor A with hPdef
  have hPpsd : P.PosSemidef := polarFactor_posSemidef A
  have hPsq : P * P = Aᴴ * A := polarFactor_mul_self A
  have hPunit : IsUnit P.det := polarFactor_isUnit_det A hA
  have hinvmul : P⁻¹ * P = 1 := nonsing_inv_mul P hPunit
  have hmulinv : P * P⁻¹ = 1 := mul_nonsing_inv P hPunit
  have hPinv_herm : (P⁻¹)ᴴ = P⁻¹ := by
    rw [conjTranspose_nonsing_inv, hPpsd.isHermitian]
  refine ⟨A * P⁻¹, ?_, ?_⟩
  · -- `A · P⁻¹` is unitary
    have hstarU : star (A * P⁻¹) = P⁻¹ * Aᴴ := by
      rw [Matrix.star_mul, star_eq_conjTranspose, star_eq_conjTranspose, hPinv_herm]
    have h1 : star (A * P⁻¹) * (A * P⁻¹) = 1 := by
      rw [hstarU]
      have e1 : P⁻¹ * Aᴴ * (A * P⁻¹) = P⁻¹ * (Aᴴ * A) * P⁻¹ := by noncomm_ring
      rw [e1, ← hPsq]
      have e2 : P⁻¹ * (P * P) * P⁻¹ = (P⁻¹ * P) * (P * P⁻¹) := by noncomm_ring
      rw [e2, hinvmul, hmulinv, one_mul]
    have h2 : (A * P⁻¹) * star (A * P⁻¹) = 1 := Matrix.mul_eq_one_comm.mp h1
    exact Unitary.mem_iff.mpr ⟨h1, h2⟩
  · -- `A = (A · P⁻¹) · P`
    rw [mul_assoc, hinvmul, mul_one]

/-! ### Full uniqueness (invertible case) -/

/-- **Uniqueness of the right polar decomposition.**  For an invertible matrix
`A`, any two right polar decompositions `A = U₁ · P₁ = U₂ · P₂` (with the `Uᵢ`
unitary and `Pᵢ` positive semidefinite) coincide. -/
theorem polar_right_unique (A U₁ P₁ U₂ P₂ : Matrix n n 𝕜) (hA : IsUnit A)
    (hU1 : U₁ ∈ unitary (Matrix n n 𝕜)) (hP1 : P₁.PosSemidef) (h1 : A = U₁ * P₁)
    (hU2 : U₂ ∈ unitary (Matrix n n 𝕜)) (hP2 : P₂.PosSemidef) (h2 : A = U₂ * P₂) :
    U₁ = U₂ ∧ P₁ = P₂ := by
  have hPeq1 : P₁ = polarFactor A := polar_psd_unique A U₁ P₁ hU1 hP1 h1
  have hPeq2 : P₂ = polarFactor A := polar_psd_unique A U₂ P₂ hU2 hP2 h2
  have hPeq : P₁ = P₂ := hPeq1.trans hPeq2.symm
  have hP1u : IsUnit P₁.det := by rw [hPeq1]; exact polarFactor_isUnit_det A hA
  have hu1 : U₁ = A * P₁⁻¹ := by
    rw [h1, mul_assoc, mul_nonsing_inv P₁ hP1u, mul_one]
  have hP2u : IsUnit P₂.det := by rw [hPeq2]; exact polarFactor_isUnit_det A hA
  have hu2 : U₂ = A * P₂⁻¹ := by
    rw [h2, mul_assoc, mul_nonsing_inv P₂ hP2u, mul_one]
  exact ⟨by rw [hu1, hu2, hPeq], hPeq⟩

/-! ### The left polar decomposition `A = √(AAᴴ) · U` -/

/-- **Left polar decomposition (invertible case).**  Every invertible matrix
`A` factors as `A = P · U` with `P = √(A Aᴴ)` positive semidefinite and `U`
unitary — the mirror image of the right decomposition, obtained by transposing
the right decomposition of `Aᴴ`. -/
theorem polar_left (A : Matrix n n 𝕜) (hA : IsUnit A) :
    ∃ P U : Matrix n n 𝕜,
      P.PosSemidef ∧ U ∈ unitary (Matrix n n 𝕜) ∧
        P = CFC.sqrt (A * Aᴴ) ∧ A = P * U := by
  have hAH : IsUnit Aᴴ := by
    refine (isUnit_iff_isUnit_det Aᴴ).mpr ?_
    rw [det_conjTranspose]
    exact ((isUnit_iff_isUnit_det A).mp hA).star
  obtain ⟨V, hV, hVeq⟩ := polar_right Aᴴ hAH
  refine ⟨polarFactor Aᴴ, Vᴴ, polarFactor_posSemidef Aᴴ, ?_, ?_, ?_⟩
  · -- `Vᴴ` is unitary
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mem hV
  · -- `polarFactor Aᴴ = √(A Aᴴ)`
    rw [polarFactor, conjTranspose_conjTranspose]
  · -- `A = polarFactor Aᴴ · Vᴴ`
    have := congrArg conjTranspose hVeq
    rw [conjTranspose_conjTranspose, conjTranspose_mul,
      (polarFactor_posSemidef Aᴴ).isHermitian] at this
    exact this

end MatrixPosDefSqrtOQ01OQ01
