import Mathlib
import Proofs.CauchyInterlacingOQ01OQ01
import Proofs.CauchyInterlacingCompression

/-
# Cauchy interlacing for principal submatrices: the eigenvalue corollary

`Proofs/CauchyInterlacingOQ01OQ01.lean` (`cauchy-interlacing-theorem-oq-01-oq-01`)
proves the **geometric identification**: the orthogonal compression of
`toEuclideanLin A` to the coordinate hyperplane
`H = span {e_{j.succAbove i}}` has, on the natural basis `e_{j.succAbove i}`,
*sesquilinear form exactly the principal submatrix*
`A.submatrix j.succAbove j.succAbove`
(`compress_inner_eq_principalSubmatrix`). It records as its first open question:

> *Assemble the matrix-level eigenvalue corollary: show
> `compress (toEuclideanLin A) H` is unitarily equivalent to
> `toEuclideanLin (A.submatrix j.succAbove j.succAbove)` via the isometry
> `e_{j.succAbove i} ↦ e_i`, so that the principal submatrix's eigenvalues
> literally interlace `A`'s (`λ_{k+1} ≤ μ_k ≤ λ_k`).*

This file answers it.  The bridge is the **coordinate isometry**
`coordEquiv : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] H`, `e_i ↦ e_{j.succAbove i}`,
under which the compression *is* `toEuclideanLin A'`:

  `compress (toEuclideanLin A) H (coordEquiv x) = coordEquiv (toEuclideanLin A' x)`
      (`compress_intertwine`).

Pushing `A'`'s spectral eigenbasis through `coordEquiv` gives an eigenbasis of
the compression with the *same antitone eigenvalues* — no eigenvalue-uniqueness
lemma is needed — which feeds the abstract `cauchy_interlacing` of
`CauchyInterlacingAssembly`.

## Main results

* `compress_intertwine` — the compression and the submatrix operator are
  intertwined by the coordinate isometry.
* `principalSubmatrix_eigenvalues_interlacing` — operator-level statement:
  the descending eigenvalues of `A` and of its principal submatrix `A'`
  interlace, `lam k.succ ≤ mu k ≤ lam k.castSucc`.
* `Matrix.IsHermitian.eigenvalues₀_principalSubmatrix_interlacing` — the literal
  matrix statement in terms of `Matrix.IsHermitian.eigenvalues₀`.

Over any `RCLike` field `𝕜` (so `ℝ` and `ℂ`). Absent from Mathlib.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace
open Matrix
open CauchyInterlacingOQ01OQ01
open CauchyInterlacing.Assembly

namespace CauchyInterlacingOQ01OQ01OQ02

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ## Eigenvalues are independent of the `finrank` proof (index bookkeeping) -/

/-- `LinearMap.IsSymmetric.eigenvalues` depends on the dimension proof only through
its right-hand side: two proofs of `finrank = m` and `finrank = m'` give the same
eigenvalue list up to the (forced) equality `m = m'`. -/
theorem eigenvalues_finrank_congr {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) {m m' : ℕ} (hm : Module.finrank 𝕜 E = m)
    (hm' : Module.finrank 𝕜 E = m') (i : Fin m) :
    hT.eigenvalues hm i = hT.eigenvalues hm' (Fin.cast (hm.symm.trans hm') i) := by
  obtain rfl : m = m' := hm.symm.trans hm'
  simp only [Fin.cast_eq_self]

/-! ## The abstract transfer engine -/

/-- **Cauchy interlacing transfers across an isometric intertwining.**

Let `T` (with antitone eigendata `b, lam`) act on `V`, let `H ≤ V` be a
codimension-one subspace, and let `T'` (with antitone eigendata `b', mu`) act on
a model space `E`.  If an isometry `e : E ≃ₗᵢ H` intertwines a symmetric operator
`TH` on `H` with `T'` (`TH (e x) = e (T' x)`) and `TH` satisfies the Rayleigh
agreement of the orthogonal compression, then the eigenvalues interlace:
`lam k.succ ≤ mu k ≤ lam k.castSucc`.

Pushing `T'`'s eigenbasis `b'` through `e` produces an eigenbasis of `TH` with the
*same* eigenvalues `mu` — so no eigenvalue-uniqueness lemma is needed — which is
fed to the abstract `cauchy_interlacing`.  Stating it for abstract `V, E` keeps
the heavy unification generic. -/
theorem interlacing_of_intertwine {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : V →ₗ[𝕜] V) (b : OrthonormalBasis (Fin (n + 1)) 𝕜 V) (lam : Fin (n + 1) → ℝ)
    (hT : ∀ i, T (b i) = (lam i : 𝕜) • b i) (hlam : Antitone lam)
    (Hs : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 Hs = n)
    (TH : Hs →ₗ[𝕜] Hs)
    (T' : E →ₗ[𝕜] E) (b' : OrthonormalBasis (Fin n) 𝕜 E) (mu : Fin n → ℝ)
    (hT' : ∀ i, T' (b' i) = (mu i : 𝕜) • b' i) (hmu : Antitone mu)
    (e : E ≃ₗᵢ[𝕜] Hs) (hinter : ∀ x : E, TH (e x) = e (T' x))
    (hRay : ∀ y : Hs, y ≠ 0 →
      RCLike.re (@inner 𝕜 Hs _ (TH y) y) / ‖y‖ ^ 2
        = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2)
    (k : Fin n) :
    lam k.succ ≤ mu k ∧ mu k ≤ lam k.castSucc := by
  set bH : OrthonormalBasis (Fin n) 𝕜 Hs := b'.map e with hbHdef
  have hbH : ∀ i, bH i = e (b' i) := fun i => OrthonormalBasis.map_apply _ _ _
  have hTH : ∀ i, TH (bH i) = (mu i : 𝕜) • bH i := by
    intro i; rw [hbH, hinter, hT', map_smul]
  exact CauchyInterlacing.Assembly.cauchy_interlacing T b lam hT hlam Hs hHdim TH bH mu
    hTH hmu hRay k

/-! ## The coordinate orthonormal basis and the coordinate isometry -/

variable (j : Fin (n + 1))

/-- The natural basis vectors of the coordinate hyperplane are orthonormal. -/
theorem orthonormal_hyperplaneBasis :
    Orthonormal 𝕜 (hyperplaneBasis (𝕜 := 𝕜) j) := by
  have hbase : Orthonormal 𝕜 (fun i : Fin n => e (𝕜 := 𝕜) (j.succAbove i)) :=
    (EuclideanSpace.orthonormal_single (𝕜 := 𝕜) (ι := Fin (n + 1))).comp _
      (Fin.succAbove_right_injective (p := j))
  rw [orthonormal_iff_ite] at hbase ⊢
  intro i i'
  rw [Submodule.coe_inner]
  exact hbase i i'

/-- The natural basis vectors span the coordinate hyperplane. -/
theorem span_hyperplaneBasis_top :
    (⊤ : Submodule 𝕜 (coordinateHyperplane (𝕜 := 𝕜) j)) ≤
      Submodule.span 𝕜 (Set.range (hyperplaneBasis (𝕜 := 𝕜) j)) := by
  rw [top_le_iff]
  apply Submodule.map_injective_of_injective
    (Submodule.subtype_injective (coordinateHyperplane (𝕜 := 𝕜) j))
  rw [Submodule.map_subtype_top, Submodule.map_span]
  have : (coordinateHyperplane (𝕜 := 𝕜) j).subtype '' Set.range (hyperplaneBasis (𝕜 := 𝕜) j)
      = Set.range (fun i : Fin n => e (𝕜 := 𝕜) (j.succAbove i)) := by
    rw [← Set.range_comp]; rfl
  rw [this, coordinateHyperplane]

/-- An orthonormal basis of the coordinate hyperplane: `coordBasis i = e_{j.succAbove i}`. -/
noncomputable def coordBasis : OrthonormalBasis (Fin n) 𝕜 (coordinateHyperplane (𝕜 := 𝕜) j) :=
  OrthonormalBasis.mk (orthonormal_hyperplaneBasis j) (span_hyperplaneBasis_top j)

@[simp] theorem coordBasis_apply (i : Fin n) :
    coordBasis (𝕜 := 𝕜) j i = hyperplaneBasis j i := by
  rw [coordBasis, OrthonormalBasis.coe_mk]

/-- The coordinate isometry `EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ H`, `e_i ↦ e_{j.succAbove i}`. -/
noncomputable def coordEquiv :
    EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] coordinateHyperplane (𝕜 := 𝕜) j :=
  (coordBasis (𝕜 := 𝕜) j).repr.symm

theorem coordEquiv_eq_sum (x : EuclideanSpace 𝕜 (Fin n)) :
    coordEquiv (𝕜 := 𝕜) j x = ∑ i, x i • coordBasis (𝕜 := 𝕜) j i := by
  rw [coordEquiv, OrthonormalBasis.sum_repr_symm]

/-- Reading off a coordinate of the isometry image against the basis returns the
input coordinate: `⟪coordBasis i', coordEquiv x⟫ = x i'`. -/
theorem coordBasis_inner_coordEquiv (x : EuclideanSpace 𝕜 (Fin n)) (i' : Fin n) :
    @inner 𝕜 _ _ (coordBasis (𝕜 := 𝕜) j i') (coordEquiv (𝕜 := 𝕜) j x) = x i' := by
  rw [← OrthonormalBasis.repr_apply_apply]
  have h : (coordBasis (𝕜 := 𝕜) j).repr (coordEquiv (𝕜 := 𝕜) j x) = x :=
    (coordBasis (𝕜 := 𝕜) j).repr.apply_symm_apply x
  rw [h]

/-! ## The intertwining: the compression is the submatrix operator -/

variable (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)

/-- Abbreviation for the principal submatrix obtained by deleting row/column `j`. -/
local notation "A'" => A.submatrix j.succAbove j.succAbove

/-- **The intertwining on a single coordinate basis vector.** This is the only
place a submodule inner product is needed, and exactly one entry is read off via
`compress_inner_eq_principalSubmatrix` — mirroring the parent file. -/
theorem compress_coordBasis (i₀ : Fin n) :
    compress (Matrix.toEuclideanLin A) (coordinateHyperplane j) (coordBasis (𝕜 := 𝕜) j i₀)
      = coordEquiv (𝕜 := 𝕜) j (Matrix.toEuclideanLin A' (EuclideanSpace.single i₀ (1 : 𝕜))) := by
  apply (coordBasis (𝕜 := 𝕜) j).repr.injective
  ext i'
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    coordBasis_inner_coordEquiv, coordBasis_apply, coordBasis_apply,
    compress_inner_eq_principalSubmatrix]
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_single, PiLp.toLp_apply,
    EuclideanSpace.ofLp_single]

/-- **The intertwining.** Under the coordinate isometry `coordEquiv`, the
orthogonal compression of `toEuclideanLin A` to the coordinate hyperplane is the
operator of the principal submatrix:

  `compress (toEuclideanLin A) H (coordEquiv x) = coordEquiv (toEuclideanLin A' x)`.

Proved by expanding `x` in the standard basis of `EuclideanSpace 𝕜 (Fin n)` and
pushing `compress`, `toEuclideanLin A'` and `coordEquiv` through the sum with
`map_sum`/`map_smul` (purely rewrite-based, so the isometry is never unfolded),
reducing each term to `compress_coordBasis`. -/
theorem compress_intertwine (x : EuclideanSpace 𝕜 (Fin n)) :
    compress (Matrix.toEuclideanLin A) (coordinateHyperplane j) (coordEquiv (𝕜 := 𝕜) j x)
      = coordEquiv (𝕜 := 𝕜) j (Matrix.toEuclideanLin A' x) := by
  have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : 𝕜) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) 𝕜).sum_repr x]
    simp_rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  rw [coordEquiv_eq_sum, map_sum]
  conv_rhs => rw [hx, map_sum]
  simp_rw [map_smul, compress_coordBasis, map_sum, map_smul]

/-! ## The eigenvalue interlacing corollary -/

variable (hA : A.IsHermitian)

/-- **Cauchy interlacing for a principal submatrix (operator-eigenvalue form).**

For a Hermitian `(n+1) × (n+1)` matrix `A` and an index `j`, write
`λ` for the descending eigenvalues of `toEuclideanLin A` and `μ` for those of the
principal submatrix `A' = A.submatrix j.succAbove j.succAbove` (delete row/column
`j`).  Then for every `k : Fin n`:

  `λ k.succ ≤ μ k`   and   `μ k ≤ λ k.castSucc`,

i.e. `λ_{k+1} ≤ μ_k ≤ λ_k`.  This is the assembly of the geometric identification
`compress_inner_eq_principalSubmatrix` (the compression of `toEuclideanLin A` to
the coordinate hyperplane *is* `toEuclideanLin A'`, via `compress_intertwine`)
with the abstract Cauchy interlacing theorem. -/
theorem principalSubmatrix_eigenvalues_interlacing (k : Fin n) :
    (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace_fin k.succ
        ≤ (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix j.succAbove)).eigenvalues
            finrank_euclideanSpace_fin k
      ∧ (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix j.succAbove)).eigenvalues
            finrank_euclideanSpace_fin k
          ≤ (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues
              finrank_euclideanSpace_fin k.castSucc := by
  -- Rayleigh agreement of the orthogonal compression.
  have hRay : ∀ y : coordinateHyperplane (𝕜 := 𝕜) j, y ≠ 0 →
      RCLike.re (@inner 𝕜 _ _
          (compress (Matrix.toEuclideanLin A) (coordinateHyperplane j) y) y) / ‖y‖ ^ 2
        = RCLike.re (@inner 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) _
            (Matrix.toEuclideanLin A (y : EuclideanSpace 𝕜 (Fin (n + 1))))
            (y : EuclideanSpace 𝕜 (Fin (n + 1)))) / ‖(y : EuclideanSpace 𝕜 (Fin (n + 1)))‖ ^ 2 := by
    intro y _
    have hi : @inner 𝕜 _ _ (compress (Matrix.toEuclideanLin A) (coordinateHyperplane j) y) y
        = @inner 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) _
            (Matrix.toEuclideanLin A (y : EuclideanSpace 𝕜 (Fin (n + 1))))
            (y : EuclideanSpace 𝕜 (Fin (n + 1))) := by
      rw [compress_apply, Submodule.inner_orthogonalProjection_eq_of_mem_right]
    rw [hi, Submodule.coe_norm]
  exact interlacing_of_intertwine
    (T := Matrix.toEuclideanLin A)
    (b := (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis finrank_euclideanSpace_fin)
    (lam := (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace_fin)
    (hT := (Matrix.isHermitian_iff_isSymmetric.1 hA).apply_eigenvectorBasis _)
    (hlam := (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues_antitone _)
    (Hs := coordinateHyperplane j) (hHdim := finrank_coordinateHyperplane j)
    (TH := compress (Matrix.toEuclideanLin A) (coordinateHyperplane j))
    (T' := Matrix.toEuclideanLin (A.submatrix j.succAbove j.succAbove))
    (b' := (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix j.succAbove)).eigenvectorBasis
      finrank_euclideanSpace_fin)
    (mu := (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix j.succAbove)).eigenvalues
      finrank_euclideanSpace_fin)
    (hT' := (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix j.succAbove)).apply_eigenvectorBasis _)
    (hmu := (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix j.succAbove)).eigenvalues_antitone _)
    (e := coordEquiv j) (hinter := compress_intertwine (A := A) (j := j)) (hRay := hRay) (k := k)

/-- **Cauchy interlacing for a principal submatrix (literal `eigenvalues₀` form).**

The descending eigenvalues `Matrix.IsHermitian.eigenvalues₀` of a Hermitian
`(n+1)×(n+1)` matrix `A` and of its principal submatrix
`A' = A.submatrix j.succAbove j.succAbove` interlace:

  `A.eigenvalues₀ (k+1) ≤ A'.eigenvalues₀ k ≤ A.eigenvalues₀ k`,

read through the index identifications `Fin (n+1) ≃ Fin (card)` and
`Fin n ≃ Fin (card)`.  This is the literal matrix statement requested by the
parent entry's open question. -/
theorem eigenvalues₀_principalSubmatrix_interlacing (k : Fin n) :
    hA.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm k.succ)
        ≤ (hA.submatrix j.succAbove).eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm k)
      ∧ (hA.submatrix j.succAbove).eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm k)
          ≤ hA.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm k.castSucc) := by
  -- `eigenvalues₀` is `eigenvalues finrank_euclideanSpace`; bridge to the
  -- `finrank_euclideanSpace_fin` indexing used in the operator statement.
  have bridgeA : ∀ i : Fin (n + 1),
      (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace_fin i
        = hA.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm i) := fun i =>
    eigenvalues_finrank_congr _ finrank_euclideanSpace_fin finrank_euclideanSpace i
  have bridgeA' : ∀ i : Fin n,
      (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix j.succAbove)).eigenvalues
          finrank_euclideanSpace_fin i
        = (hA.submatrix j.succAbove).eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm i) :=
    fun i => eigenvalues_finrank_congr _ finrank_euclideanSpace_fin finrank_euclideanSpace i
  obtain ⟨hlo, hup⟩ := principalSubmatrix_eigenvalues_interlacing j A hA k
  rw [bridgeA, bridgeA'] at hlo
  rw [bridgeA', bridgeA] at hup
  exact ⟨hlo, hup⟩

end CauchyInterlacingOQ01OQ01OQ02
