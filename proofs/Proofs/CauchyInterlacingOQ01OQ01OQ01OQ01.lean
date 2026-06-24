import Proofs.CauchyInterlacingOQ01OQ01OQ01

/-
# Sorted Eigenvalues Are a Unitary Invariant

The parent entry (`cauchy-interlacing-theorem-oq-01-oq-01-oq-01`) proves the **bridge lemma**
`eigenvalues_eq_of_eigenbasis`: a self-adjoint operator's *sorted* eigenvalue list is determined
by *any* orthonormal eigenbasis with antitone real eigenvalues.  Its docstring records — but does
not formalize — the headline corollary singled out as that entry's lead open question:

> **The sorted spectrum is invariant under unitary (isometric) conjugation.**

This file isolates that corollary as a reusable lemma.

* `isSymmetric_of_isometryConj` — symmetry transports across an isometric intertwiner: if
  `e : E ≃ₗᵢ F` is a linear isometry equivalence with `S (e x) = e (T x)` and `T` is symmetric,
  then `S` is symmetric.  (So the symmetry hypothesis on `S` below is *automatic*, recorded here
  for completeness.)

* `eigenvalues_isometryConj` — the main result: for symmetric `T : E →ₗ[𝕜] E`, `S : F →ₗ[𝕜] F`
  and a linear isometry equivalence `e : E ≃ₗᵢ F` intertwining them (`S (e x) = e (T x)`, i.e.
  `S = e ∘ T ∘ e⁻¹`), the sorted eigenvalue tuples coincide: `hS.eigenvalues hnF = hT.eigenvalues hnE`.

The proof is exactly the recipe sketched in the parent: transport `T`'s canonical orthonormal
eigenbasis through `e` to obtain an orthonormal eigenbasis of `S` *with the same antitone eigenvalue
tuple* `f = hT.eigenvalues hnE`, then feed it to `eigenvalues_eq_of_eigenbasis`.  The eigenbasis
condition `S (b i) = f i • b i` is immediate from the intertwining relation and the parent's
`apply_eigenvectorBasis`.

This is the tool that finishes principal-submatrix Cauchy interlacing: the orthogonal compression
of a Hermitian `A` to a coordinate hyperplane is the isometric conjugate of the principal-submatrix
operator, so this lemma identifies their sorted spectra.

Holds over any `RCLike` field `𝕜` (so `ℝ` and `ℂ`), with `0` sorries and `0` axioms.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace
open Matrix Polynomial

namespace CauchyInterlacingOQ01OQ01OQ01OQ01

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Symmetry transports across an isometric intertwiner.** If `e : E ≃ₗᵢ F` satisfies
`S (e x) = e (T x)` (so `S = e ∘ T ∘ e⁻¹`) and `T` is symmetric, then so is `S`.  Hence the
symmetry hypothesis on `S` in `eigenvalues_isometryConj` is automatic. -/
theorem isSymmetric_of_isometryConj {T : E →ₗ[𝕜] E} {S : F →ₗ[𝕜] F}
    (hT : T.IsSymmetric) (e : E ≃ₗᵢ[𝕜] F) (hes : ∀ x, S (e x) = e (T x)) :
    S.IsSymmetric := by
  intro y z
  obtain ⟨x, rfl⟩ := e.surjective y
  obtain ⟨x', rfl⟩ := e.surjective z
  rw [hes, hes, e.inner_map_map, e.inner_map_map]
  exact hT x x'

/-- **Unitary conjugation invariance of the sorted spectrum.** For symmetric `T : E →ₗ[𝕜] E` and
`S : F →ₗ[𝕜] F` related by a linear isometry equivalence `e : E ≃ₗᵢ F` with `S (e x) = e (T x)`,
the sorted eigenvalue tuples are equal. -/
theorem eigenvalues_isometryConj {T : E →ₗ[𝕜] E} {S : F →ₗ[𝕜] F}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (e : E ≃ₗᵢ[𝕜] F)
    (hes : ∀ x, S (e x) = e (T x))
    {n : ℕ} (hnE : Module.finrank 𝕜 E = n) (hnF : Module.finrank 𝕜 F = n) :
    hS.eigenvalues hnF = hT.eigenvalues hnE := by
  -- Transport `T`'s canonical eigenbasis through `e`.
  set b : OrthonormalBasis (Fin n) 𝕜 F := (hT.eigenvectorBasis hnE).map e with hb_def
  -- `b` is an orthonormal eigenbasis of `S` for the *same* eigenvalue tuple.
  have hb : ∀ i, S (b i) = ((hT.eigenvalues hnE i : ℝ) : 𝕜) • b i := by
    intro i
    have hmap : b i = e ((hT.eigenvectorBasis hnE) i) := by
      rw [hb_def, OrthonormalBasis.map_apply]
    rw [hmap, hes, hT.apply_eigenvectorBasis hnE i, map_smul]
  -- Apply the parent's bridge lemma.
  exact CauchyInterlacingOQ01OQ01OQ01.eigenvalues_eq_of_eigenbasis hS hnF b
    (hT.eigenvalues hnE) (hT.eigenvalues_antitone hnE) hb

end CauchyInterlacingOQ01OQ01OQ01OQ01
