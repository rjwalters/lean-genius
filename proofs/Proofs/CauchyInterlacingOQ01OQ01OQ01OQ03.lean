import Mathlib
import Proofs.CauchyInterlacingPoincare
import Proofs.CauchyInterlacingOQ01OQ01

/-
# Poincaré separation for m×m principal submatrices (matrix form)

`Proofs/CauchyInterlacingOQ01OQ01OQ02.lean` proves **codimension-one** Cauchy
interlacing at the level of concrete matrices: for a Hermitian
`(n+1) × (n+1)` matrix `A` and one deleted index `j`, the eigenvalues of the
principal submatrix `A.submatrix j.succAbove j.succAbove` interlace those of `A`,
`λ_{k+1} ≤ μ_k ≤ λ_k`. The single deleted coordinate is encoded by the specific
injection `j.succAbove : Fin n ↪ Fin (n+1)`.

Separately, `Proofs/CauchyInterlacingPoincare.lean` proves the **abstract**
Poincaré separation theorem for an *arbitrary*-codimension compression: for a
symmetric operator on a space of dimension `n + m` compressed to a subspace of
dimension `n`, `λ_{k+m} ≤ μ_k ≤ λ_k`.

This file joins the two, delivering the theorem the whole chain was building
toward: **Poincaré separation at the level of concrete matrices for an arbitrary
`n × n` principal submatrix**. Fix a Hermitian `(n+m) × (n+m)` matrix `A` and an
injective index map `ι : Fin n → Fin (n+m)` (choosing which `n` of the `n+m`
rows/columns to keep). Then the eigenvalues of the principal submatrix
`A.submatrix ι ι` separate those of `A`:

  `λ_{k+m}(A) ≤ μ_k(A.submatrix ι ι) ≤ λ_k(A)`,     for every `k : Fin n`.

The mechanism generalises the codimension-one file verbatim, replacing the
specific injection `j.succAbove` by an arbitrary injective `ι`:

* The coordinate subspace `H = span {e_{ι i}}` (the span of the kept coordinate
  axes) is `n`-dimensional (`finrank_coordSubspace`, using injectivity of `ι`).
* The orthogonal compression of `toEuclideanLin A` to `H`, read on the basis
  `(e_{ι i})`, is exactly `A.submatrix ι ι` (`compress_inner_eq_submatrix`).
* Under the coordinate isometry `coordEquiv : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ H`,
  `e_i ↦ e_{ι i}`, the compression *is* the submatrix operator
  (`compress_intertwine`), so pushing the submatrix's spectral eigenbasis through
  `coordEquiv` yields an eigenbasis of the compression with the *same* antitone
  eigenvalues — feeding the abstract `poincare_separation` with no
  eigenvalue-uniqueness lemma required (`interlacing_poincare_of_intertwine`).

## Main results

* `principalSubmatrix_poincare_separation` — operator-eigenvalue form:
  `λ_{k+m} ≤ μ_k ≤ λ_k` for the descending eigenvalues of `toEuclideanLin A` and
  of `toEuclideanLin (A.submatrix ι ι)`.
* `eigenvalues₀_principalSubmatrix_poincare` — the literal matrix statement in
  terms of `Matrix.IsHermitian.eigenvalues₀`.

The codimension-one file is the special case `m = 1`, `ι = j.succAbove`. Over any
`RCLike` field `𝕜` (so `ℝ` and `ℂ`). Absent from Mathlib.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace
open Matrix
open CauchyInterlacingOQ01OQ01
open CauchyInterlacing.Poincare

namespace CauchyInterlacingOQ01OQ01OQ01OQ03

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}

/-! ## Eigenvalues are independent of the `finrank` proof (index bookkeeping) -/

/-- `LinearMap.IsSymmetric.eigenvalues` depends on the dimension proof only through
its right-hand side: two proofs of `finrank = p` and `finrank = p'` give the same
eigenvalue list up to the (forced) equality `p = p'`. -/
theorem eigenvalues_finrank_congr {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) {p p' : ℕ} (hp : Module.finrank 𝕜 E = p)
    (hp' : Module.finrank 𝕜 E = p') (i : Fin p) :
    hT.eigenvalues hp i = hT.eigenvalues hp' (Fin.cast (hp.symm.trans hp') i) := by
  obtain rfl : p = p' := hp.symm.trans hp'
  simp only [Fin.cast_eq_self]

/-! ## The Poincaré transfer engine -/

/-- **Poincaré separation transfers across an isometric intertwining.**

Let `T` (with antitone eigendata `b, lam`) act on `V` of dimension `n + m`, let
`Hs ≤ V` have dimension `n` (codimension `m`), and let `T'` (with antitone
eigendata `b', mu`) act on a model space `E`. If an isometry `ee' : E ≃ₗᵢ Hs`
intertwines a symmetric operator `TH` on `Hs` with `T'` (`TH (ee' x) = ee' (T' x)`)
and `TH` satisfies the Rayleigh agreement of the orthogonal compression, then the
eigenvalues separate: `lam ⟨k+m⟩ ≤ mu k ≤ lam ⟨k⟩`.

Pushing `T'`'s eigenbasis `b'` through `ee'` produces an eigenbasis of `TH` with
the *same* eigenvalues `mu` — so no eigenvalue-uniqueness lemma is needed — which
is fed to the abstract `poincare_separation`. This is the arbitrary-codimension
analogue of `interlacing_of_intertwine` from the codimension-one file. -/
theorem interlacing_poincare_of_intertwine {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : V →ₗ[𝕜] V) (b : OrthonormalBasis (Fin (n + m)) 𝕜 V) (lam : Fin (n + m) → ℝ)
    (hT : ∀ i, T (b i) = (lam i : 𝕜) • b i) (hlam : Antitone lam)
    (Hs : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 Hs = n)
    (TH : Hs →ₗ[𝕜] Hs)
    (T' : E →ₗ[𝕜] E) (b' : OrthonormalBasis (Fin n) 𝕜 E) (mu : Fin n → ℝ)
    (hT' : ∀ i, T' (b' i) = (mu i : 𝕜) • b' i) (hmu : Antitone mu)
    (ee' : E ≃ₗᵢ[𝕜] Hs) (hinter : ∀ x : E, TH (ee' x) = ee' (T' x))
    (hRay : ∀ y : Hs, y ≠ 0 →
      RCLike.re (@inner 𝕜 Hs _ (TH y) y) / ‖y‖ ^ 2
        = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2)
    (k : Fin n) :
    lam ⟨(k : ℕ) + m, by have := k.isLt; omega⟩ ≤ mu k
      ∧ mu k ≤ lam ⟨(k : ℕ), by have := k.isLt; omega⟩ := by
  set bH : OrthonormalBasis (Fin n) 𝕜 Hs := b'.map ee' with hbHdef
  have hbH : ∀ i, bH i = ee' (b' i) := fun i => OrthonormalBasis.map_apply _ _ _
  have hTH : ∀ i, TH (bH i) = (mu i : 𝕜) • bH i := by
    intro i; rw [hbH, hinter, hT', map_smul]
  exact poincare_separation T b lam hT hlam Hs hHdim TH bH mu hTH hmu hRay k

/-! ## The coordinate subspace and coordinate isometry for a general injection -/

/-- The standard basis vector `e_a = single a 1` of `EuclideanSpace 𝕜 (Fin (n+m))`. -/
noncomputable abbrev ee (a : Fin (n + m)) : EuclideanSpace 𝕜 (Fin (n + m)) :=
  EuclideanSpace.single a (1 : 𝕜)

/-- **Matrix entries via inner products of basis vectors.** Viewing `A` as the
operator `toEuclideanLin A`, the `(a, b)` entry is `⟪e_a, A e_b⟫`. -/
theorem inner_single_toEuclideanLin_single (A : Matrix (Fin (n + m)) (Fin (n + m)) 𝕜)
    (a b : Fin (n + m)) :
    @inner 𝕜 _ _ (ee (𝕜 := 𝕜) a) (Matrix.toEuclideanLin A (ee b)) = A a b := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  show (Matrix.toEuclideanLin A (EuclideanSpace.single b (1 : 𝕜))) a = A a b
  rw [Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single_one]
  rfl

variable (ι : Fin n → Fin (n + m))

/-- The **coordinate subspace** for an index map `ι`: the span of the `n` standard
basis vectors `e_{ι i}` (the coordinate axes kept by the principal submatrix). -/
noncomputable def coordSubspace : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin (n + m))) :=
  Submodule.span 𝕜 (Set.range fun i : Fin n => ee (𝕜 := 𝕜) (ι i))

/-- `e_{ι i}` lies in the coordinate subspace. -/
theorem mem_coordSubspace (i : Fin n) :
    ee (𝕜 := 𝕜) (ι i) ∈ coordSubspace (𝕜 := 𝕜) ι :=
  Submodule.subset_span ⟨i, rfl⟩

/-- The `i`-th natural basis vector of the coordinate subspace, as a subspace element. -/
noncomputable def coordVec (i : Fin n) : coordSubspace (𝕜 := 𝕜) ι :=
  ⟨ee (ι i), mem_coordSubspace ι i⟩

/-- The natural basis vectors of the coordinate subspace are orthonormal
(uses injectivity of `ι`). -/
theorem orthonormal_coordVec (hι : Function.Injective ι) :
    Orthonormal 𝕜 (coordVec (𝕜 := 𝕜) ι) := by
  have hbase : Orthonormal 𝕜 (fun i : Fin n => ee (𝕜 := 𝕜) (ι i)) :=
    (EuclideanSpace.orthonormal_single (𝕜 := 𝕜) (ι := Fin (n + m))).comp _ hι
  rw [orthonormal_iff_ite] at hbase ⊢
  intro i i'
  rw [Submodule.coe_inner]
  exact hbase i i'

/-- The natural basis vectors span the coordinate subspace. -/
theorem span_coordVec_top :
    (⊤ : Submodule 𝕜 (coordSubspace (𝕜 := 𝕜) ι)) ≤
      Submodule.span 𝕜 (Set.range (coordVec (𝕜 := 𝕜) ι)) := by
  rw [top_le_iff]
  apply Submodule.map_injective_of_injective
    (Submodule.subtype_injective (coordSubspace (𝕜 := 𝕜) ι))
  rw [Submodule.map_subtype_top, Submodule.map_span]
  have : (coordSubspace (𝕜 := 𝕜) ι).subtype '' Set.range (coordVec (𝕜 := 𝕜) ι)
      = Set.range (fun i : Fin n => ee (𝕜 := 𝕜) (ι i)) := by
    rw [← Set.range_comp]; rfl
  rw [this, coordSubspace]

/-- An orthonormal basis of the coordinate subspace: `coordBasis i = e_{ι i}`. -/
noncomputable def coordBasis (hι : Function.Injective ι) :
    OrthonormalBasis (Fin n) 𝕜 (coordSubspace (𝕜 := 𝕜) ι) :=
  OrthonormalBasis.mk (orthonormal_coordVec ι hι) (span_coordVec_top ι)

@[simp] theorem coordBasis_apply (hι : Function.Injective ι) (i : Fin n) :
    coordBasis (𝕜 := 𝕜) ι hι i = coordVec ι i := by
  rw [coordBasis, OrthonormalBasis.coe_mk]

/-- The coordinate isometry `EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ H`, `e_i ↦ e_{ι i}`. -/
noncomputable def coordEquiv (hι : Function.Injective ι) :
    EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] coordSubspace (𝕜 := 𝕜) ι :=
  (coordBasis (𝕜 := 𝕜) ι hι).repr.symm

theorem coordEquiv_eq_sum (hι : Function.Injective ι) (x : EuclideanSpace 𝕜 (Fin n)) :
    coordEquiv (𝕜 := 𝕜) ι hι x = ∑ i, x i • coordBasis (𝕜 := 𝕜) ι hι i := by
  rw [coordEquiv, OrthonormalBasis.sum_repr_symm]

/-- Reading off a coordinate of the isometry image against the basis returns the
input coordinate: `⟪coordBasis i', coordEquiv x⟫ = x i'`. -/
theorem coordBasis_inner_coordEquiv (hι : Function.Injective ι)
    (x : EuclideanSpace 𝕜 (Fin n)) (i' : Fin n) :
    @inner 𝕜 _ _ (coordBasis (𝕜 := 𝕜) ι hι i') (coordEquiv (𝕜 := 𝕜) ι hι x) = x i' := by
  rw [← OrthonormalBasis.repr_apply_apply]
  have h : (coordBasis (𝕜 := 𝕜) ι hι).repr (coordEquiv (𝕜 := 𝕜) ι hι x) = x :=
    (coordBasis (𝕜 := 𝕜) ι hι).repr.apply_symm_apply x
  rw [h]

/-- The coordinate subspace has dimension `n`: it is a codimension-`m` subspace of
the `(n+m)`-dimensional ambient space. -/
theorem finrank_coordSubspace (hι : Function.Injective ι) :
    Module.finrank 𝕜 (coordSubspace (𝕜 := 𝕜) ι) = n := by
  have hli : LinearIndependent 𝕜 (fun i : Fin n => ee (𝕜 := 𝕜) (ι i)) :=
    ((EuclideanSpace.orthonormal_single (𝕜 := 𝕜) (ι := Fin (n + m))).comp _ hι).linearIndependent
  rw [coordSubspace, finrank_span_eq_card hli, Fintype.card_fin]

/-! ## The intertwining: the compression is the submatrix operator -/

variable (A : Matrix (Fin (n + m)) (Fin (n + m)) 𝕜)

/-- **Main identification.** The orthogonal compression of `toEuclideanLin A` to
the coordinate subspace `H`, read as a sesquilinear form on the natural basis
`(e_{ι i})` of `H`, is exactly the principal submatrix `A.submatrix ι ι`:

`⟪e_{ι i'}, compress (toEuclideanLin A) H e_{ι i}⟫ = (A.submatrix ι ι) i' i`. -/
theorem compress_inner_eq_submatrix (hι : Function.Injective ι) (i i' : Fin n) :
    @inner 𝕜 _ _ (coordBasis (𝕜 := 𝕜) ι hι i')
        (compress (Matrix.toEuclideanLin A) (coordSubspace ι) (coordBasis (𝕜 := 𝕜) ι hι i))
      = (A.submatrix ι ι) i' i := by
  rw [coordBasis_apply, coordBasis_apply, inner_compress_eq]
  exact inner_single_toEuclideanLin_single A (ι i') (ι i)

/-- **The intertwining on a single coordinate basis vector.** -/
theorem compress_coordBasis (hι : Function.Injective ι) (i₀ : Fin n) :
    compress (Matrix.toEuclideanLin A) (coordSubspace ι) (coordBasis (𝕜 := 𝕜) ι hι i₀)
      = coordEquiv (𝕜 := 𝕜) ι hι
          (Matrix.toEuclideanLin (A.submatrix ι ι) (EuclideanSpace.single i₀ (1 : 𝕜))) := by
  apply (coordBasis (𝕜 := 𝕜) ι hι).repr.injective
  ext i'
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    coordBasis_inner_coordEquiv, compress_inner_eq_submatrix]
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_single, PiLp.toLp_apply,
    EuclideanSpace.ofLp_single]

/-- **The intertwining.** Under the coordinate isometry `coordEquiv`, the
orthogonal compression of `toEuclideanLin A` to the coordinate subspace is the
operator of the principal submatrix `A.submatrix ι ι`:

  `compress (toEuclideanLin A) H (coordEquiv x) = coordEquiv (toEuclideanLin A' x)`. -/
theorem compress_intertwine (hι : Function.Injective ι) (x : EuclideanSpace 𝕜 (Fin n)) :
    compress (Matrix.toEuclideanLin A) (coordSubspace ι) (coordEquiv (𝕜 := 𝕜) ι hι x)
      = coordEquiv (𝕜 := 𝕜) ι hι (Matrix.toEuclideanLin (A.submatrix ι ι) x) := by
  have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : 𝕜) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) 𝕜).sum_repr x]
    simp_rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  rw [coordEquiv_eq_sum, map_sum]
  conv_rhs => rw [hx, map_sum]
  simp_rw [map_smul, compress_coordBasis, map_sum, map_smul]

/-! ## The eigenvalue interlacing corollary -/

/-- **Poincaré separation for a principal submatrix (operator-eigenvalue form).**

For a Hermitian `(n+m) × (n+m)` matrix `A` and an injective index map
`ι : Fin n → Fin (n+m)`, write `λ` for the descending eigenvalues of
`toEuclideanLin A` and `μ` for those of the `n × n` principal submatrix
`A.submatrix ι ι`. Then for every `k : Fin n`:

  `λ ⟨k+m⟩ ≤ μ k`   and   `μ k ≤ λ ⟨k⟩`,

i.e. `λ_{k+m} ≤ μ_k ≤ λ_k`. This is the assembly of the geometric identification
`compress_intertwine` with the abstract `poincare_separation`. The
codimension-one `principalSubmatrix_eigenvalues_interlacing` is the special case
`m = 1`, `ι = j.succAbove`. -/
theorem principalSubmatrix_poincare_separation
    (hA : A.IsHermitian) (hι : Function.Injective ι) (k : Fin n) :
    (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace_fin
          ⟨(k : ℕ) + m, by have := k.isLt; omega⟩
        ≤ (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix ι)).eigenvalues
            finrank_euclideanSpace_fin k
      ∧ (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix ι)).eigenvalues
            finrank_euclideanSpace_fin k
          ≤ (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace_fin
              ⟨(k : ℕ), by have := k.isLt; omega⟩ := by
  -- Rayleigh agreement of the orthogonal compression.
  have hRay : ∀ y : coordSubspace (𝕜 := 𝕜) ι, y ≠ 0 →
      RCLike.re (@inner 𝕜 _ _
          (compress (Matrix.toEuclideanLin A) (coordSubspace ι) y) y) / ‖y‖ ^ 2
        = RCLike.re (@inner 𝕜 (EuclideanSpace 𝕜 (Fin (n + m))) _
            (Matrix.toEuclideanLin A (y : EuclideanSpace 𝕜 (Fin (n + m))))
            (y : EuclideanSpace 𝕜 (Fin (n + m)))) /
            ‖(y : EuclideanSpace 𝕜 (Fin (n + m)))‖ ^ 2 := by
    intro y _
    have hi : @inner 𝕜 _ _ (compress (Matrix.toEuclideanLin A) (coordSubspace ι) y) y
        = @inner 𝕜 (EuclideanSpace 𝕜 (Fin (n + m))) _
            (Matrix.toEuclideanLin A (y : EuclideanSpace 𝕜 (Fin (n + m))))
            (y : EuclideanSpace 𝕜 (Fin (n + m))) := by
      rw [compress_apply, Submodule.inner_orthogonalProjection_eq_of_mem_right]
    rw [hi, Submodule.coe_norm]
  exact interlacing_poincare_of_intertwine
    (T := Matrix.toEuclideanLin A)
    (b := (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis finrank_euclideanSpace_fin)
    (lam := (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace_fin)
    (hT := (Matrix.isHermitian_iff_isSymmetric.1 hA).apply_eigenvectorBasis _)
    (hlam := (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues_antitone _)
    (Hs := coordSubspace ι) (hHdim := finrank_coordSubspace ι hι)
    (TH := compress (Matrix.toEuclideanLin A) (coordSubspace ι))
    (T' := Matrix.toEuclideanLin (A.submatrix ι ι))
    (b' := (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix ι)).eigenvectorBasis
      finrank_euclideanSpace_fin)
    (mu := (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix ι)).eigenvalues
      finrank_euclideanSpace_fin)
    (hT' := (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix ι)).apply_eigenvectorBasis _)
    (hmu := (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix ι)).eigenvalues_antitone _)
    (ee' := coordEquiv ι hι)
    (hinter := compress_intertwine (𝕜 := 𝕜) (ι := ι) (A := A) hι)
    (hRay := hRay) (k := k)

/-- **Poincaré separation for a principal submatrix (literal `eigenvalues₀` form).**

The descending eigenvalues `Matrix.IsHermitian.eigenvalues₀` of a Hermitian
`(n+m) × (n+m)` matrix `A` and of its `n × n` principal submatrix
`A.submatrix ι ι` (for injective `ι`) separate:

  `A.eigenvalues₀ ⟨k+m⟩ ≤ (A.submatrix ι ι).eigenvalues₀ k ≤ A.eigenvalues₀ ⟨k⟩`,

read through the index identifications `Fin (n+m) ≃ Fin (card)` and
`Fin n ≃ Fin (card)`. This is the literal matrix statement of the Poincaré
separation theorem for arbitrary principal submatrices. -/
theorem eigenvalues₀_principalSubmatrix_poincare
    (hA : A.IsHermitian) (hι : Function.Injective ι) (k : Fin n) :
    hA.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm ⟨(k : ℕ) + m, by have := k.isLt; omega⟩)
        ≤ (hA.submatrix ι).eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm k)
      ∧ (hA.submatrix ι).eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm k)
          ≤ hA.eigenvalues₀
              (Fin.cast (Fintype.card_fin _).symm ⟨(k : ℕ), by have := k.isLt; omega⟩) := by
  have bridgeA : ∀ i : Fin (n + m),
      (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace_fin i
        = hA.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm i) := fun i =>
    eigenvalues_finrank_congr _ finrank_euclideanSpace_fin finrank_euclideanSpace i
  have bridgeA' : ∀ i : Fin n,
      (Matrix.isHermitian_iff_isSymmetric.1 (hA.submatrix ι)).eigenvalues
          finrank_euclideanSpace_fin i
        = (hA.submatrix ι).eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm i) :=
    fun i => eigenvalues_finrank_congr _ finrank_euclideanSpace_fin finrank_euclideanSpace i
  obtain ⟨hlo, hup⟩ := principalSubmatrix_poincare_separation (𝕜 := 𝕜) (ι := ι) A hA hι k
  rw [bridgeA, bridgeA'] at hlo
  rw [bridgeA', bridgeA] at hup
  exact ⟨hlo, hup⟩

end CauchyInterlacingOQ01OQ01OQ01OQ03
