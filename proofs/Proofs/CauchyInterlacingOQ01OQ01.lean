import Mathlib

/-
# The Orthogonal Compression to a Coordinate Hyperplane Is the Principal Submatrix

`Proofs/CauchyInterlacingCompression.lean` builds, for a symmetric operator `T` on a finite
dimensional inner product space `V` and a codimension-one subspace `H ≤ V`, the **orthogonal
compression**

  `compress T H := P_H ∘ T ∘ ι_H : H →ₗ[𝕜] H`,

and proves its eigenvalues interlace those of `T` (`cauchy_interlacing_compression`). Its
docstring asserts — but does not prove — that *"for a Hermitian matrix and a coordinate
hyperplane this is exactly the principal submatrix obtained by deleting a row and column."*
That identification is the first open question left by that file.

This file proves it. Fix a square matrix `A : Matrix (Fin (n+1)) (Fin (n+1)) 𝕜`, an index
`j`, and view `A` as the operator `toEuclideanLin A` on `EuclideanSpace 𝕜 (Fin (n+1))`. Take
the coordinate hyperplane

  `H = span 𝕜 { e_{j.succAbove i} : i : Fin n }`,

the span of the `n` standard basis vectors *other than* `e_j`. We show that the sesquilinear
form of the orthogonal compression `compress (toEuclideanLin A) H`, read off on the natural
orthonormal basis `(e_{j.succAbove i})` of `H`, is **exactly** the principal submatrix
`A.submatrix j.succAbove j.succAbove` obtained by deleting row `j` and column `j`:

  `⟪e_{j.succAbove i'}, compress (toEuclideanLin A) H e_{j.succAbove i}⟫
      = A (j.succAbove i') (j.succAbove i)`.    (`compress_inner_eq_principalSubmatrix`)

The two ingredients are (i) the orthogonal-projection adjoint identity, which collapses the
compression's inner product on `H` to `T`'s inner product on `V`
(`inner_compress_eq`), and (ii) the elementary entry formula
`⟪e_a, toEuclideanLin A e_b⟫ = A a b` (`inner_single_toEuclideanLin_single`).

We also record that the principal submatrix is Hermitian when `A` is
(`isHermitian_principalSubmatrix`), and that the coordinate hyperplane really is `n`
dimensional (`finrank_coordinateHyperplane`), so that this identification slots directly into
`cauchy_interlacing_compression` to yield interlacing of the principal submatrix's
eigenvalues. The eigenvalue-level corollary itself is left for follow-up.

All results hold over any `RCLike` field `𝕜` (so `ℝ` and `ℂ`). Absent from Mathlib.
-/

open scoped InnerProductSpace
open Matrix

namespace CauchyInterlacingOQ01OQ01

section Compress

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- The orthogonal **compression** of `T` to a subspace `H`: project `T ↑y` back into `H`.
This mirrors `CauchyInterlacing.Compression.compress`; it is reproduced here so the file is
self-contained. -/
noncomputable def compress (T : V →ₗ[𝕜] V) (H : Submodule 𝕜 V) : H →ₗ[𝕜] H :=
  (H.orthogonalProjection : V →L[𝕜] H).toLinearMap ∘ₗ (T ∘ₗ H.subtype)

@[simp] theorem compress_apply (T : V →ₗ[𝕜] V) (H : Submodule 𝕜 V) (y : H) :
    compress T H y = H.orthogonalProjection (T (y : V)) := rfl

/-- **The compression's inner product collapses to `T`'s.** On `H`, the sesquilinear form of
the orthogonal compression equals that of `T` on the ambient space: the orthogonal projection
is invisible to inner products with vectors already in `H`. -/
theorem inner_compress_eq (T : V →ₗ[𝕜] V) (H : Submodule 𝕜 V) (y z : H) :
    @inner 𝕜 H _ y (compress T H z) = @inner 𝕜 V _ (y : V) (T (z : V)) := by
  rw [compress_apply, Submodule.inner_orthogonalProjection_eq_of_mem_left]

end Compress

section Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The standard basis vector `e_a = single a 1` of `EuclideanSpace 𝕜 (Fin (n+1))`. -/
noncomputable abbrev e (a : Fin (n + 1)) : EuclideanSpace 𝕜 (Fin (n + 1)) :=
  EuclideanSpace.single a (1 : 𝕜)

/-- **Matrix entries via inner products of basis vectors.** Viewing `A` as the operator
`toEuclideanLin A`, the `(a, b)` entry is recovered as `⟪e_a, A e_b⟫`. -/
theorem inner_single_toEuclideanLin_single (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)
    (a b : Fin (n + 1)) :
    @inner 𝕜 _ _ (e a) (Matrix.toEuclideanLin A (e b)) = A a b := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  show (Matrix.toEuclideanLin A (EuclideanSpace.single b (1 : 𝕜))) a = A a b
  rw [Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single_one]
  rfl

variable (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (j : Fin (n + 1))

/-- The **coordinate hyperplane** for index `j`: the span of the `n` standard basis vectors
`e_{j.succAbove i}`, i.e. every standard basis vector except `e_j`. -/
noncomputable def coordinateHyperplane : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) :=
  Submodule.span 𝕜 (Set.range fun i : Fin n => e (𝕜 := 𝕜) (j.succAbove i))

/-- `e_{j.succAbove i}` lies in the coordinate hyperplane. -/
theorem mem_coordinateHyperplane (i : Fin n) :
    e (𝕜 := 𝕜) (j.succAbove i) ∈ coordinateHyperplane (𝕜 := 𝕜) j :=
  Submodule.subset_span ⟨i, rfl⟩

/-- The `i`-th natural basis vector of the coordinate hyperplane, as an element of the
subspace. -/
noncomputable def hyperplaneBasis (i : Fin n) : coordinateHyperplane (𝕜 := 𝕜) j :=
  ⟨e (j.succAbove i), mem_coordinateHyperplane j i⟩

/-- **Main identification.** The orthogonal compression of `toEuclideanLin A` to the
coordinate hyperplane `H`, evaluated as a sesquilinear form on the natural basis
`(e_{j.succAbove i})` of `H`, is exactly the principal submatrix of `A` obtained by deleting
row `j` and column `j`:

`⟪e_{j.succAbove i'}, compress (toEuclideanLin A) H e_{j.succAbove i}⟫
    = (A.submatrix j.succAbove j.succAbove) i' i`. -/
theorem compress_inner_eq_principalSubmatrix (i i' : Fin n) :
    @inner 𝕜 _ _ (hyperplaneBasis j i')
        (compress (Matrix.toEuclideanLin A) (coordinateHyperplane j) (hyperplaneBasis j i))
      = (A.submatrix j.succAbove j.succAbove) i' i := by
  rw [inner_compress_eq]
  exact inner_single_toEuclideanLin_single A (j.succAbove i') (j.succAbove i)

/-- The principal submatrix obtained by deleting row `j` and column `j` is Hermitian whenever
`A` is. Together with the identification above, the compression is a Hermitian operator with
matrix the principal submatrix. -/
theorem isHermitian_principalSubmatrix (hA : A.IsHermitian) :
    (A.submatrix j.succAbove j.succAbove).IsHermitian :=
  hA.submatrix j.succAbove

/-- The coordinate hyperplane has dimension `n`: it is a genuine codimension-one subspace of
the `(n+1)`-dimensional ambient space, so it is exactly the kind of hyperplane
`cauchy_interlacing_compression` expects. -/
theorem finrank_coordinateHyperplane :
    Module.finrank 𝕜 (coordinateHyperplane (𝕜 := 𝕜) (n := n) j) = n := by
  classical
  have hortho : Orthonormal 𝕜 (fun i : Fin n => e (𝕜 := 𝕜) (j.succAbove i)) := by
    have hbase : Orthonormal 𝕜 (fun a : Fin (n + 1) => e (𝕜 := 𝕜) a) :=
      EuclideanSpace.orthonormal_single (𝕜 := 𝕜) (ι := Fin (n + 1))
    exact hbase.comp _ (Fin.succAbove_right_injective (p := j))
  have hli : LinearIndependent 𝕜 (fun i : Fin n => e (𝕜 := 𝕜) (j.succAbove i)) :=
    hortho.linearIndependent
  rw [coordinateHyperplane, finrank_span_eq_card hli, Fintype.card_fin]

end Matrix

end CauchyInterlacingOQ01OQ01
