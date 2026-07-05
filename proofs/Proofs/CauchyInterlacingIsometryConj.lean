import Mathlib
import Proofs.CauchyInterlacingOQ01OQ01OQ01

/-
# Unitary conjugation invariance of the sorted spectrum

`CauchyInterlacingOQ01OQ01OQ01.lean` (#27958, 0-sorry/0-axiom) proves the **bridge lemma**

> `eigenvalues_eq_of_eigenbasis` — if `(b, f)` is *any* orthonormal eigenbasis of a self-adjoint
> `T` with `f` antitone, then `hT.eigenvalues = f`,

and records — in its docstring, but *without formalizing it* — the immediate corollary that a
self-adjoint operator's sorted eigenvalue list is invariant under unitary (isometric)
conjugation.  That corollary is the *single fact* flagged as future work by three interlacing
entries (#25063 keystone, #27917 principal-submatrix identification, #27958 this bridge): it is
the tool needed to read the abstract compression-form Cauchy interlacing
(`cauchy_interlacing_compression`) off as the familiar *principal-submatrix* interlacing.

This file formalizes that corollary:

* `eigenvalues_isometryConj` — if `S` and `T` are self-adjoint operators intertwined by a linear
  isometry equivalence `e : E ≃ₗᵢ[𝕜] F` (so `S ∘ e = e ∘ T`, i.e. `S = e ∘ T ∘ e⁻¹`), then they
  have the *same* sorted eigenvalue list: `hS.eigenvalues = hT.eigenvalues`.

The proof is a direct specialization of the bridge lemma: transport `T`'s canonical eigenbasis
`hT.eigenvectorBasis` through `e` to an orthonormal eigenbasis `(hT.eigenvectorBasis).map e` of
`S` carrying the *same* antitone eigenvalue tuple `hT.eigenvalues`, then feed it to
`eigenvalues_eq_of_eigenbasis`.  Holds over any `RCLike` field `𝕜` (so `ℝ` and `ℂ`).

## Roadmap: finishing the matrix-level principal-submatrix corollary

With `eigenvalues_isometryConj` in hand, the headline matrix statement

  `λ_{k+1}(A) ≤ λ_k(A⁽ʲ⁾) ≤ λ_k(A)`     (`A⁽ʲ⁾ := A.submatrix j.succAbove j.succAbove`)

for Hermitian `A : Matrix (Fin (n+1)) (Fin (n+1)) 𝕜` and index `j` is assembled as follows.
Let `V := EuclideanSpace 𝕜 (Fin (n+1))`, `T := toEuclideanLin A`, and `H := coordinateHyperplane j`
(the span of the `n` standard basis vectors `e_{j.succAbove i}`), with `finrank V = n+1`,
`finrank H = n` (`CauchyInterlacingOQ01OQ01.finrank_coordinateHyperplane`).

1. **Interlace `T` with its compression.**  `CauchyInterlacing.Compression.cauchy_interlacing_compression`
   gives `(hT.eigenvalues) k.succ ≤ (isSymmetric_compress hT H).eigenvalues k ≤ (hT.eigenvalues) k.castSucc`.

2. **Identify the compression with the submatrix operator.**  Build the isometry
   `φ : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] H` from the orthonormal family
   `hyperplaneBasis j : Fin n → H` (orthonormal in `H` by restriction of the standard basis of `V`;
   `n = finrank H`, so it is an `OrthonormalBasis` via `Orthonormal.toOrthonormalBasis` /
   `OrthonormalBasis.repr`).  Then `compress (toEuclideanLin A) H = φ ∘ toEuclideanLin A⁽ʲ⁾ ∘ φ⁻¹`,
   proved on the standard basis by comparing inner products against `hyperplaneBasis j i'`:
   both sides give `A⁽ʲ⁾ i' i` — the LHS by `compress_inner_eq_principalSubmatrix`, the RHS by
   `inner_single_toEuclideanLin_single` for `A⁽ʲ⁾` plus the isometry property of `φ` — and an
   orthonormal basis separates vectors (`OrthonormalBasis.repr` injective).

3. **Transfer eigenvalues.**  Apply `eigenvalues_isometryConj` with `e := φ⁻¹` to get
   `(isSymmetric_compress hT H).eigenvalues = (toEuclideanLin A⁽ʲ⁾).IsSymmetric.eigenvalues`.
   Substituting into step 1 yields interlacing between the sorted spectra of the operators
   `toEuclideanLin A` and `toEuclideanLin A⁽ʲ⁾` — the matrix-level statement.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace

namespace CauchyInterlacingOQ01OQ01OQ01

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Unitary conjugation invariance of the sorted spectrum.**  If `S : F →ₗ[𝕜] F` and
`T : E →ₗ[𝕜] E` are self-adjoint operators intertwined by a linear isometry equivalence
`e : E ≃ₗᵢ[𝕜] F` — that is `S (e x) = e (T x)` for all `x`, equivalently `S = e ∘ T ∘ e⁻¹` —
then their sorted (antitone) eigenvalue lists coincide: `hS.eigenvalues = hT.eigenvalues`.

The image basis `(hT.eigenvectorBasis).map e` is an orthonormal eigenbasis of `S` with the same
antitone eigenvalue tuple `hT.eigenvalues`, so the bridge lemma `eigenvalues_eq_of_eigenbasis`
identifies `S`'s sorted eigenvalues with it. -/
theorem eigenvalues_isometryConj {T : E →ₗ[𝕜] E} {S : F →ₗ[𝕜] F}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (e : E ≃ₗᵢ[𝕜] F)
    (he : ∀ x, S (e x) = e (T x))
    {n : ℕ} (hnE : Module.finrank 𝕜 E = n) (hnF : Module.finrank 𝕜 F = n) :
    hS.eigenvalues hnF = hT.eigenvalues hnE := by
  refine eigenvalues_eq_of_eigenbasis hS hnF
    ((hT.eigenvectorBasis hnE).map e) (hT.eigenvalues hnE)
    (hT.eigenvalues_antitone hnE) ?_
  intro i
  rw [OrthonormalBasis.map_apply, he, hT.apply_eigenvectorBasis hnE]
  simp [map_smul]

end CauchyInterlacingOQ01OQ01OQ01
