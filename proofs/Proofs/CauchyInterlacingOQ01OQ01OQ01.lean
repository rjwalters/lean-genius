import Mathlib

/-
# Sorted Eigenvalues Are Determined by Any Orthonormal Eigenbasis

`CauchyInterlacingKeystone.lean` and the principal-submatrix identification
(`cauchy-interlacing-theorem-oq-01-oq-01`, #27917) both flag the same step as "future work":
*bridging the abstract operator eigenvalues `LinearMap.IsSymmetric.eigenvalues` to the concrete
`Matrix.IsHermitian.eigenvalues₀`*, so that the compression-form Cauchy interlacing can be read
off as the familiar principal-submatrix interlacing.

The single mathematical fact powering that bridge — and absent from Mathlib — is:

> **A self-adjoint operator's *sorted* eigenvalue list is determined by the operator alone.**

Equivalently, the sorted eigenvalues are invariant under unitary (isometric) conjugation.  This
file proves it via the characteristic polynomial:

* `eigenvalues_eq_of_eigenbasis` — if `(b, f)` is *any* orthonormal eigenbasis of a self-adjoint
  `T` (so `T (b i) = f i • b i`) with `f` antitone, then `hT.eigenvalues = f`.  The matrix of
  `T` in `b` is `diagonal f`, so `T.charpoly = ∏ (X − f i)`; equating this with the canonical
  eigenbasis gives equal *root multisets*, and two antitone tuples with the same multiset are
  equal by uniqueness of the sorted enumeration (`List.eq_of_perm_of_sorted`).

As an immediate corollary (recorded in the docstring of `eigenvalues_eq_of_eigenbasis` and as the
lead open question of this entry), if `S = e ∘ T ∘ e⁻¹` for a linear isometry equivalence
`e : E ≃ₗᵢ F`, then `S` and `T` have the same sorted eigenvalue list: transport `T`'s canonical
eigenbasis through `e` to get an orthonormal eigenbasis of `S` with the *same* antitone eigenvalue
tuple, and apply the bridge.  That is exactly the tool needed to finish principal-submatrix
Cauchy interlacing — the orthogonal compression of a Hermitian `A` to the coordinate hyperplane
`e_jᗮ` is the isometric conjugate of the principal-submatrix operator
`toEuclideanLin (A.submatrix j.succAbove j.succAbove)` (the sesquilinear-form identification of
#27917), so the bridge identifies their sorted spectra and the parent's
`cauchy_interlacing_compression` reads off as `λ_{k+1}(A) ≤ λ_k(A⁽ʲ⁾) ≤ λ_k(A)`.

Holds over any `RCLike` field `𝕜` (so `ℝ` and `ℂ`), with `0` sorries and `0` axioms.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace
open Matrix Polynomial

namespace CauchyInterlacingOQ01OQ01OQ01

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
/-- In an orthonormal eigenbasis `b` with (real) eigenvalues `f`, the matrix of `T` is diagonal. -/
theorem toMatrix_diagonal_of_eigenbasis {T : E →ₗ[𝕜] E} {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E) (f : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (f i : 𝕜) • b i) :
    LinearMap.toMatrix b.toBasis b.toBasis T = Matrix.diagonal (fun i => (f i : 𝕜)) := by
  ext i l
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hb l, map_smul, Finsupp.smul_apply,
    ← OrthonormalBasis.coe_toBasis, Module.Basis.repr_self, Finsupp.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : i = l <;> simp [h, eq_comm]

/-- The characteristic polynomial of `T` factors through any orthonormal eigenbasis. -/
theorem charpoly_eq_prod_of_eigenbasis {T : E →ₗ[𝕜] E} {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E) (f : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (f i : 𝕜) • b i) :
    T.charpoly = ∏ i, (X - C (f i : 𝕜)) := by
  rw [← LinearMap.charpoly_toMatrix T b.toBasis, toMatrix_diagonal_of_eigenbasis b f hb,
    Matrix.charpoly_diagonal]

/-- **Bridge lemma.** A self-adjoint operator's *sorted* eigenvalues are determined by *any*
orthonormal eigenbasis with antitone (real) eigenvalues.  The proof matches the characteristic
polynomial `∏ (X − f i)` against that of the canonical eigenbasis and invokes uniqueness of the
sorted enumeration of the common root multiset.

**Corollary (unitary conjugation invariance).** Specializing `b := (hT.eigenvectorBasis hE).map e`
and `f := hT.eigenvalues hE` for a linear isometry equivalence `e : E ≃ₗᵢ F` with
`S (e x) = e (T x)` shows `hS.eigenvalues hF = hT.eigenvalues hE`: the sorted spectrum is a
unitary invariant. -/
theorem eigenvalues_eq_of_eigenbasis {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (f : Fin n → ℝ) (hf : Antitone f)
    (hb : ∀ i, T (b i) = (f i : 𝕜) • b i) :
    hT.eigenvalues hn = f := by
  have h1 : (∏ i, (X - C (hT.eigenvalues hn i : 𝕜))) = ∏ i, (X - C (f i : 𝕜)) := by
    rw [← charpoly_eq_prod_of_eigenbasis (hT.eigenvectorBasis hn) _ (hT.apply_eigenvectorBasis hn),
      ← charpoly_eq_prod_of_eigenbasis b f hb]
  have hmap : ∀ g : Fin n → ℝ, (∏ i, (X - C (g i : 𝕜)))
      = (Multiset.map (fun a => X - C a) (Finset.univ.val.map (fun i => (g i : 𝕜)))).prod := by
    intro g; rw [Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
  have hroots𝕜 : (Finset.univ.val.map (fun i => (hT.eigenvalues hn i : 𝕜)))
      = (Finset.univ.val.map (fun i => (f i : 𝕜))) := by
    have := congrArg Polynomial.roots h1
    rwa [hmap, hmap, Polynomial.roots_multiset_prod_X_sub_C,
      Polynomial.roots_multiset_prod_X_sub_C] at this
  have hrootsR : (Finset.univ.val.map (hT.eigenvalues hn)) = (Finset.univ.val.map f) := by
    apply Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜))
    simpa only [Multiset.map_map, Function.comp_def] using hroots𝕜
  have hperm : (List.ofFn (hT.eigenvalues hn)).Perm (List.ofFn f) := by
    apply (Multiset.coe_eq_coe).1
    simpa [List.ofFn_eq_map] using hrootsR
  have hsort₁ : (List.ofFn (hT.eigenvalues hn)).Pairwise (· ≥ ·) :=
    List.pairwise_ofFn.2 (fun {_ _} hij => (hT.eigenvalues_antitone hn) hij.le)
  have hsort₂ : (List.ofFn f).Pairwise (· ≥ ·) :=
    List.pairwise_ofFn.2 (fun {_ _} hij => hf hij.le)
  have := List.eq_of_perm_of_sorted (le := (· ≥ ·))
    (fun a b _ _ hab hba => le_antisymm hba hab) hsort₁ hsort₂ hperm
  exact List.ofFn_inj.1 this

end CauchyInterlacingOQ01OQ01OQ01
