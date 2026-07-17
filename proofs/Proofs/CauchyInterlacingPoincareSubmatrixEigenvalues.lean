import Mathlib
import Proofs.CauchyInterlacingPoincareSubmatrix

/-
# Poincaré separation in native `Matrix.IsHermitian.eigenvalues₀` form

`CauchyInterlacingPoincareSubmatrix.lean` proves the principal-submatrix Poincaré
separation theorem `poincare_separation_submatrix`, but phrases its eigenvalues
through the *operator* layer: `(isHermitian_iff_isSymmetric.1 hA).eigenvalues`,
i.e. `LinearMap.IsSymmetric.eigenvalues` of `toEuclideanLin A`, using the finrank
witness `finrank_euclideanSpace_fin : finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n+m))) = n+m`.

That entry's first open question asks to restate the conclusion with Mathlib's
native matrix eigenvalues `Matrix.IsHermitian.eigenvalues₀`, threading the
`Fintype.card (Fin (n+m)) = n+m` reindexing so the signature is *fully matrix
facing*.  This file supplies that restatement.

## The reindexing obstruction

`Matrix.IsHermitian.eigenvalues₀ hA : Fin (Fintype.card (Fin (n+m))) → ℝ` is
*defined* as `(isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace`
— the **same** operator eigenvalues, but built from the finrank witness
`finrank_euclideanSpace : finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n+m))) = Fintype.card (Fin (n+m))`.
The two witnesses differ only in their right-hand side, and
`Fintype.card (Fin (n+m)) = n+m` is **not** definitional (it unfolds through
`List.length_finRange`), so `eigenvalues₀` and the submatrix theorem's `lam`/`mu`
do not agree on the nose; a `Fin.cast` sits between them.

The bridge is `LinearMap.IsSymmetric.eigenvalues_cast`: the operator eigenvalues
are independent of *which* finrank proof is used — beyond the forced `Fin.cast`
between the (propositionally equal) index bounds — because once the two natural
numbers are identified the two witnesses are equal by proof irrelevance and the
`Fin.cast` collapses to the identity.  With that in hand, `eigenvalues₀` reduces
verbatim to the operator eigenvalues at the reindexed coordinate, and the
matrix-facing interlacing follows from `poincare_separation_submatrix` with no
new spectral content.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace Matrix
open Matrix WithLp

namespace CauchyInterlacing.PoincareSubmatrix

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}

/-! ### The finrank-witness bridge for symmetric-operator eigenvalues -/

/-- The sorted eigenvalues of a symmetric operator do not depend on *which* proof
`finrank 𝕜 E = N` is supplied, beyond the canonical `Fin.cast` between the two
index bounds.  Once the two dimensions are identified, the two finrank witnesses
agree by proof irrelevance and the cast is the identity. -/
theorem _root_.LinearMap.IsSymmetric.eigenvalues_cast
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {N₁ N₂ : ℕ} (h₁ : Module.finrank 𝕜 E = N₁) (h₂ : Module.finrank 𝕜 E = N₂)
    (i : Fin N₁) :
    hT.eigenvalues h₁ i = hT.eigenvalues h₂ (Fin.cast (h₁.symm.trans h₂) i) := by
  obtain rfl : N₁ = N₂ := h₁.symm.trans h₂
  have hi : Fin.cast (h₁.symm.trans h₂) i = i := Fin.ext rfl
  rw [hi]

/-- `Matrix.IsHermitian.eigenvalues₀` is the operator eigenvalues built with the
`finrank_euclideanSpace_fin` witness, at the coordinate reindexed by the canonical
`Fintype.card (Fin N) = N` cast.  (`eigenvalues₀` itself uses `finrank_euclideanSpace`.) -/
theorem eigenvalues₀_eq_op {N : ℕ} {B : Matrix (Fin N) (Fin N) 𝕜} (hB : B.IsHermitian)
    (i : Fin (Fintype.card (Fin N))) :
    hB.eigenvalues₀ i
      = (Matrix.isHermitian_iff_isSymmetric.1 hB).eigenvalues finrank_euclideanSpace_fin
          (Fin.cast (Fintype.card_fin N) i) := by
  have hdef : hB.eigenvalues₀ i
      = (Matrix.isHermitian_iff_isSymmetric.1 hB).eigenvalues finrank_euclideanSpace i := rfl
  rw [hdef]
  exact (Matrix.isHermitian_iff_isSymmetric.1 hB).eigenvalues_cast
    finrank_euclideanSpace finrank_euclideanSpace_fin i

/-! ### The matrix Poincaré separation theorem in `eigenvalues₀` form -/

/-- **Poincaré separation / Cauchy interlacing — native matrix eigenvalue form.**

Let `A` be a Hermitian `(n+m) × (n+m)` matrix over `𝕜`, and let
`e : Fin n → Fin (n+m)` be an injective choice of retained coordinates, so
`A.submatrix e e` is the principal submatrix obtained by deleting the `m`
complementary rows and columns.  Writing `λ := hA.eigenvalues₀` (descending
eigenvalues of `A`, indexed by `Fin (Fintype.card (Fin (n+m)))`) and
`μ := (hA.submatrix e).eigenvalues₀` (descending eigenvalues of the principal
submatrix), the two spectra interlace:

  `λ ⟨k+m⟩ ≤ μ ⟨k⟩`   and   `μ ⟨k⟩ ≤ λ ⟨k⟩`   for every `k : Fin n`.

This is the parent entry's `poincare_separation_submatrix` restated purely
through Mathlib's `Matrix.IsHermitian.eigenvalues₀`, closing that entry's first
open question. -/
theorem poincare_separation_submatrix_eigenvalues₀
    (A : Matrix (Fin (n + m)) (Fin (n + m)) 𝕜) (hA : A.IsHermitian)
    (e : Fin n → Fin (n + m)) (he : Function.Injective e) (k : Fin n) :
    hA.eigenvalues₀ ⟨(k : ℕ) + m, by rw [Fintype.card_fin]; have := k.isLt; omega⟩
        ≤ (hA.submatrix e).eigenvalues₀ ⟨(k : ℕ), by rw [Fintype.card_fin]; exact k.isLt⟩
    ∧ (hA.submatrix e).eigenvalues₀ ⟨(k : ℕ), by rw [Fintype.card_fin]; exact k.isLt⟩
        ≤ hA.eigenvalues₀ ⟨(k : ℕ), by rw [Fintype.card_fin]; have := k.isLt; omega⟩ := by
  obtain ⟨hlow, hup⟩ := poincare_separation_submatrix A hA e he k
  -- Rewrite every `eigenvalues₀` back to the operator eigenvalues used by the parent.
  simp only [eigenvalues₀_eq_op]
  -- The remaining `Fin.cast`s of the explicit index literals collapse to the
  -- parent's literals; `hlow`/`hup` are exactly the goals up to `Fin.ext`.
  refine ⟨?_, ?_⟩
  · convert hlow using 2 <;> exact Fin.ext rfl
  · convert hup using 2 <;> exact Fin.ext rfl

end CauchyInterlacing.PoincareSubmatrix
