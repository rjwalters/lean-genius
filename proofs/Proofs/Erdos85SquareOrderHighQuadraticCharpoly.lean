import Mathlib
import Proofs.Erdos85SquareOrderHighQuadraticSector

/-!
# Reducing-subspace bridge for the square-order quadratic sector

The square-order high-difference family spans an adjacency-invariant subspace.
For a symmetric operator, invariance of a subspace automatically gives
invariance of its orthogonal complement.  This small bridge allows the
characteristic-polynomial factorization over a reducing subspace to be applied
without constructing an explicit commuting projection.
-/

open scoped InnerProductSpace

namespace Erdos85

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A symmetric linear operator preserves the orthogonal complement of every
invariant subspace. -/
theorem orthogonal_invariant_of_isSymmetric
    {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric)
    (H : Submodule ℝ V) (hH : ∀ x ∈ H, T x ∈ H) :
    ∀ y ∈ Hᗮ, T y ∈ Hᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro x hx
  rw [← hT x y]
  exact hy (T x) (hH x hx)

/-- Characteristic polynomials multiply across a finite block-diagonal
matrix. -/
theorem charpoly_blockDiagonal
    {R n o : Type*} [CommRing R] [DecidableEq n] [Fintype n]
    [DecidableEq o] [Fintype o] (M : o → Matrix n n R) :
    (Matrix.blockDiagonal M).charpoly = ∏ k, (M k).charpoly := by
  unfold Matrix.charpoly
  have hcharmatrix :
      (Matrix.blockDiagonal M).charmatrix =
        Matrix.blockDiagonal (fun k => (M k).charmatrix) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hkl : k = l
    · subst l
      by_cases hij : i = j <;>
        simp [Matrix.blockDiagonal_apply, hij]
    · simp [Matrix.blockDiagonal_apply, hkl]
  rw [hcharmatrix, Matrix.det_blockDiagonal]

def quadraticPairMatrix {R : Type*} [CommRing R] (d : R) :
    Matrix Bool Bool R
  | false, false => 0
  | false, true => d
  | true, false => 1
  | true, true => 0

theorem quadraticPairMatrix_charpoly
    {R : Type*} [CommRing R] (d : R) :
    (quadraticPairMatrix d).charpoly =
      Polynomial.X ^ 2 - Polynomial.C d := by
  unfold Matrix.charpoly
  rw [← Matrix.det_reindex_self finTwoEquiv.symm
    (quadraticPairMatrix d).charmatrix]
  rw [Matrix.det_fin_two]
  simp [Matrix.reindex_apply, quadraticPairMatrix, finTwoEquiv]
  ring

theorem reindex_quadraticExchangeMatrix
    {R E : Type*} [CommRing R] [Fintype E] [DecidableEq E] (d : R) :
    Matrix.reindex (Equiv.boolProdEquivSum E).symm
        (Equiv.boolProdEquivSum E).symm
        (Matrix.fromBlocks (0 : Matrix E E R)
          (d • (1 : Matrix E E R)) (1 : Matrix E E R) 0) =
      Matrix.blockDiagonal (fun _ : E => quadraticPairMatrix d) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  cases i <;> cases j <;> by_cases hkl : k = l <;>
    simp [Matrix.reindex_apply, Matrix.blockDiagonal_apply,
      quadraticPairMatrix, hkl]

theorem quadraticExchangeMatrix_charpoly
    {R E : Type*} [CommRing R] [Fintype E] [DecidableEq E] (d : R) :
    (Matrix.fromBlocks (0 : Matrix E E R)
        (d • (1 : Matrix E E R)) (1 : Matrix E E R) 0).charpoly =
      (Polynomial.X ^ 2 - Polynomial.C d) ^ Fintype.card E := by
  rw [← Matrix.charpoly_reindex (Equiv.boolProdEquivSum E).symm]
  rw [reindex_quadraticExchangeMatrix, charpoly_blockDiagonal]
  simp [quadraticPairMatrix_charpoly]

/-- The characteristic polynomial of adjacency restricted to the rational high
quadratic sector is the expected power of the quadratic factor. -/
theorem squareOrder_highQuadraticSector_restrict_charpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    LinearMap.charpoly
        (LinearMap.restrict (G.adjMatrix ℚ).toLin'
          (squareOrder_highQuadraticSector_span_invariant
            G hfree hd hmin hcard ha)) =
      (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)) ^
        Fintype.card {x // x ∈ (squareOrderHighVertices G d).erase a} := by
  let B := squareOrderHighQuadraticSectorBasis
    G hfree hd hmin hcover hcard ha
  rw [← LinearMap.charpoly_toMatrix
    (LinearMap.restrict (G.adjMatrix ℚ).toLin'
      (squareOrder_highQuadraticSector_span_invariant
        G hfree hd hmin hcard ha)) B]
  rw [squareOrder_highQuadraticSector_restrict_toMatrix
    G hfree hd hmin hcover hcard ha]
  exact quadraticExchangeMatrix_charpoly (d : ℚ)

end

end Erdos85
