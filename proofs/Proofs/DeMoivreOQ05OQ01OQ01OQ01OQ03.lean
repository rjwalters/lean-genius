/-
The normalised DFT as an explicit linear isometric isomorphism of ℂⁿ

Source: Open question from the de-moivre gallery family
        (de-moivre-oq-05-oq-01-oq-01-oq-01, third open question)
Status: VERIFIED (0 axioms, 0 sorries)

The parent entry (de-moivre-oq-05-oq-01-oq-01-oq-01) packaged the normalised
discrete Fourier transform `U(j,k) = exp(2πi·jk/n)/√n` as a *matrix* and proved

      U · Uᴴ = 1,   i.e.   U ∈ Matrix.unitaryGroup (Fin n) ℂ,

together with the ℓ²-energy law `‖Ux‖ = ‖x‖`.  Its third open question asks to
upgrade this matrix-level unitarity to a genuine **isometric isomorphism** of the
Euclidean space `ℂⁿ = EuclideanSpace ℂ (Fin n)`, i.e. an element of

      EuclideanSpace ℂ (Fin n)  ≃ₗᵢ[ℂ]  EuclideanSpace ℂ (Fin n).

This file does exactly that.  Acting on `EuclideanSpace ℂ (Fin n)` by the
matrix–vector product, `U` becomes a linear map `toEuclideanLin U`; the parent's
unitarity makes it inner-product preserving and two-sided invertible, so it
assembles into a `LinearIsometryEquiv`, `dftLIE`.  We then record the three
defining properties — it acts as `toEuclideanLin U`, preserves the norm and the
inner product — and identify its inverse with `toEuclideanLin Uᴴ`, the **inverse
discrete Fourier transform**.  Since `U` is unitary, `Uᴴ = U⁻¹`, so the inverse
isometry is literally the conjugate-transpose / inverse-DFT operator.

Proof.  Write `f = toEuclideanLin U`.  Mathlib's
`toEuclideanLin_conjTranspose_eq_adjoint` gives `adjoint f = toEuclideanLin Uᴴ`,
and the matrix identities `Uᴴ·U = 1` and `U·Uᴴ = 1` (both forms of
`U ∈ unitaryGroup`) show `toEuclideanLin Uᴴ` is a two-sided inverse of `f`.  Hence
`⟪f x, f y⟫ = ⟪x, adjoint f (f y)⟫ = ⟪x, y⟫`, so `f` preserves the inner product
(`LinearMap.isometryOfInner`), and the right inverse makes it surjective
(`LinearIsometryEquiv.ofSurjective`).

Theorems / definitions:
1. `dftMatrix_conjTranspose_toEuclideanLin_left_inverse`  — Uᴴ∘U = id on ℂⁿ
2. `dftMatrix_toEuclideanLin_right_inverse`               — U∘Uᴴ = id on ℂⁿ
3. `dftMatrix_toEuclideanLin_inner`                       — ⟪Ux,Uy⟫ = ⟪x,y⟫
4. `dftLIE`                                               — the LinearIsometryEquiv
5. `dftLIE_apply`                                         — dftLIE = toEuclideanLin U
6. `dftLIE_norm`                                          — ‖dftLIE x‖ = ‖x‖
7. `dftLIE_inner`                                         — ⟪dftLIE x, dftLIE y⟫ = ⟪x,y⟫
8. `dftLIE_symm_apply`                                    — (dftLIE)⁻¹ = toEuclideanLin Uᴴ
-/

import Mathlib
import Proofs.DeMoivreOQ05OQ01OQ01OQ01

open Matrix DeMoivreOQ05OQ01OQ01OQ01

namespace DeMoivreOQ05OQ01OQ01OQ01OQ03

/-- **`Uᴴ` is a left inverse of `U` as operators on `ℂⁿ`.**
On `EuclideanSpace ℂ (Fin n)`, applying `toEuclideanLin Uᴴ` after `toEuclideanLin U`
is the identity, because the matrix identity `Uᴴ · U = 1` (the `star A * A = 1`
form of `U ∈ unitaryGroup`) collapses the composed matrix–vector product. -/
theorem dftMatrix_conjTranspose_toEuclideanLin_left_inverse (n : ℕ) (hn : 0 < n)
    (z : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanLin (dftMatrix n)ᴴ (Matrix.toEuclideanLin (dftMatrix n) z) = z := by
  have hAA : (dftMatrix n)ᴴ * dftMatrix n = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp (dftMatrix_mem_unitaryGroup n hn)
    rwa [Matrix.star_eq_conjTranspose] at h
  apply WithLp.ofLp_injective 2
  simp only [Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]

/-- **`Uᴴ` is a right inverse of `U` as operators on `ℂⁿ`.**
Symmetrically, applying `toEuclideanLin U` after `toEuclideanLin Uᴴ` is the
identity, using the matrix identity `U · Uᴴ = 1`.  Together with the left-inverse
lemma this exhibits `toEuclideanLin U` as a bijection of `ℂⁿ`. -/
theorem dftMatrix_toEuclideanLin_right_inverse (n : ℕ) (hn : 0 < n)
    (w : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanLin (dftMatrix n) (Matrix.toEuclideanLin (dftMatrix n)ᴴ w) = w := by
  have hAA : dftMatrix n * (dftMatrix n)ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp (dftMatrix_mem_unitaryGroup n hn)
    rwa [Matrix.star_eq_conjTranspose] at h
  apply WithLp.ofLp_injective 2
  simp only [Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]

/-- **The DFT operator preserves the Hermitian inner product.**
For all `x, y ∈ ℂⁿ`, `⟪Ux, Uy⟫ = ⟪x, y⟫`.  This is the operator-theoretic core of
unitarity: writing the left side via the adjoint, `⟪Ux, Uy⟫ = ⟪x, U*(Uy)⟫`, and the
adjoint `U* = toEuclideanLin Uᴴ` is a left inverse of `U`, so `U*(Uy) = y`. -/
theorem dftMatrix_toEuclideanLin_inner (n : ℕ) (hn : 0 < n)
    (x y : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (Matrix.toEuclideanLin (dftMatrix n) x)
        (Matrix.toEuclideanLin (dftMatrix n) y) : ℂ) = inner ℂ x y := by
  rw [show (inner ℂ (Matrix.toEuclideanLin (dftMatrix n) x)
            (Matrix.toEuclideanLin (dftMatrix n) y) : ℂ)
        = inner ℂ x (LinearMap.adjoint (Matrix.toEuclideanLin (dftMatrix n))
            (Matrix.toEuclideanLin (dftMatrix n) y))
      from (LinearMap.adjoint_inner_right _ _ _).symm,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    dftMatrix_conjTranspose_toEuclideanLin_left_inverse n hn]

/-- **The normalised DFT as a linear isometric isomorphism of `ℂⁿ`.**
The operator `toEuclideanLin U` preserves the inner product and is surjective (its
right inverse is `toEuclideanLin Uᴴ`), so it packages into an element of
`EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)` — the discrete Fourier
transform as a genuine unitary of the Hilbert space `ℂⁿ`. -/
noncomputable def dftLIE (n : ℕ) (hn : 0 < n) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometryEquiv.ofSurjective
    ((Matrix.toEuclideanLin (dftMatrix n)).isometryOfInner
      (dftMatrix_toEuclideanLin_inner n hn))
    (fun w => ⟨Matrix.toEuclideanLin (dftMatrix n)ᴴ w, by
      simpa only [LinearMap.coe_isometryOfInner] using
        dftMatrix_toEuclideanLin_right_inverse n hn w⟩)

/-- `dftLIE` acts as the matrix operator `toEuclideanLin U`. -/
@[simp]
theorem dftLIE_apply (n : ℕ) (hn : 0 < n) (x : EuclideanSpace ℂ (Fin n)) :
    dftLIE n hn x = Matrix.toEuclideanLin (dftMatrix n) x := by
  rw [dftLIE, LinearIsometryEquiv.coe_ofSurjective, LinearMap.coe_isometryOfInner]

/-- **`dftLIE` preserves the Euclidean norm:** `‖dftLIE x‖ = ‖x‖`.  This is the
ℓ²-energy law of the parent entry, now packaged as the `norm_map` of an isometry. -/
theorem dftLIE_norm (n : ℕ) (hn : 0 < n) (x : EuclideanSpace ℂ (Fin n)) :
    ‖dftLIE n hn x‖ = ‖x‖ :=
  (dftLIE n hn).norm_map x

/-- **`dftLIE` preserves the Hermitian inner product:** `⟪dftLIE x, dftLIE y⟫ = ⟪x, y⟫`. -/
theorem dftLIE_inner (n : ℕ) (hn : 0 < n) (x y : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (dftLIE n hn x) (dftLIE n hn y) : ℂ) = inner ℂ x y :=
  (dftLIE n hn).inner_map_map x y

/-- **The inverse isometry is the inverse / conjugate-transpose DFT.**
`(dftLIE)⁻¹` acts as `toEuclideanLin Uᴴ`.  Since `U` is unitary, `Uᴴ = U⁻¹`, so the
inverse of the forward transform is exactly the inverse discrete Fourier transform
`x(k) = (1/n)∑_j x̂(j)·exp(-2πi·jk/n)` realised by the conjugate-transpose matrix. -/
theorem dftLIE_symm_apply (n : ℕ) (hn : 0 < n) (w : EuclideanSpace ℂ (Fin n)) :
    (dftLIE n hn).symm w = Matrix.toEuclideanLin (dftMatrix n)ᴴ w := by
  apply (dftLIE n hn).injective
  rw [LinearIsometryEquiv.apply_symm_apply, dftLIE_apply]
  exact (dftMatrix_toEuclideanLin_right_inverse n hn w).symm

end DeMoivreOQ05OQ01OQ01OQ01OQ03
