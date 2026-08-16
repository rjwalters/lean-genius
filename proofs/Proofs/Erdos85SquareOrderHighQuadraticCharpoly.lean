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

/-- The characteristic polynomial of the restriction to an invariant
subspace divides the ambient characteristic polynomial. -/
theorem restrict_charpoly_dvd_charpoly
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (T : W →ₗ[K] W)
    (H : Submodule K W) (hH : ∀ x ∈ H, T x ∈ H) :
    LinearMap.charpoly (LinearMap.restrict T hH) ∣ LinearMap.charpoly T := by
  classical
  obtain ⟨Q, hQ⟩ := H.exists_isCompl
  let e := Submodule.prodEquivOfIsCompl H Q hQ
  let bH := Module.Free.chooseBasis K H
  let bQ := Module.Free.chooseBasis K Q
  let b := bH.prod bQ
  let F : (H × Q) →ₗ[K] (H × Q) := e.symm.conj T
  let M := LinearMap.toMatrix b b F
  have hM21 : M.toBlocks₂₁ = 0 := by
    ext i j
    change M (Sum.inr i) (Sum.inl j) = 0
    rw [show M (Sum.inr i) (Sum.inl j) =
        ((bH.prod bQ).repr
          (F ((bH.prod bQ) (Sum.inl j)))) (Sum.inr i) by
      simpa [M, b] using
        LinearMap.toMatrix_apply b b F (Sum.inr i) (Sum.inl j)]
    rw [show (bH.prod bQ) (Sum.inl j) = (bH j, 0) by simp]
    simp only [F, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    change ((bH.prod bQ).repr
      (e.symm (T (e (bH j, 0))))) (Sum.inr i) = 0
    have hmem : T (bH j : W) ∈ H := hH _ (bH j).property
    rw [show e (bH j, 0) = (bH j : W) by
      simp [e, Submodule.coe_prodEquivOfIsCompl']]
    rw [show e.symm (T (bH j : W)) =
        (⟨T (bH j : W), hmem⟩, 0) by
      exact Submodule.prodEquivOfIsCompl_symm_apply_left H Q hQ
        ⟨T (bH j : W), hmem⟩]
    simp
  have hM11 :
      M.toBlocks₁₁ =
        LinearMap.toMatrix bH bH (LinearMap.restrict T hH) := by
    ext i j
    change M (Sum.inl i) (Sum.inl j) =
      LinearMap.toMatrix bH bH (LinearMap.restrict T hH) i j
    rw [show M (Sum.inl i) (Sum.inl j) =
        ((bH.prod bQ).repr
          (F ((bH.prod bQ) (Sum.inl j)))) (Sum.inl i) by
      simpa [M, b] using
        LinearMap.toMatrix_apply b b F (Sum.inl i) (Sum.inl j)]
    rw [LinearMap.toMatrix_apply]
    rw [show (bH.prod bQ) (Sum.inl j) = (bH j, 0) by simp]
    simp only [F, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    change ((bH.prod bQ).repr
      (e.symm (T (e (bH j, 0))))) (Sum.inl i) =
        bH.repr ((LinearMap.restrict T hH) (bH j)) i
    have hmem : T (bH j : W) ∈ H := hH _ (bH j).property
    rw [show e (bH j, 0) = (bH j : W) by
      simp [e, Submodule.coe_prodEquivOfIsCompl']]
    rw [show e.symm (T (bH j : W)) =
        (⟨T (bH j : W), hmem⟩, 0) by
      exact Submodule.prodEquivOfIsCompl_symm_apply_left H Q hQ
        ⟨T (bH j : W), hmem⟩]
    rfl
  refine ⟨M.toBlocks₂₂.charpoly, ?_⟩
  rw [← LinearMap.charpoly_toMatrix
    (LinearMap.restrict T hH) bH]
  rw [← hM11]
  rw [← Matrix.charpoly_fromBlocks_zero₂₁]
  rw [show Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ = M by
    rw [← hM21, Matrix.fromBlocks_toBlocks]]
  rw [LinearMap.charpoly_toMatrix]
  exact (LinearEquiv.charpoly_conj e.symm T).symm

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

/-- The high-sector quadratic polynomial divides the full rational adjacency
characteristic polynomial. -/
theorem squareOrder_highQuadraticFactor_dvd_adjMatrixRat_charpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)) ^
        Fintype.card {x // x ∈ (squareOrderHighVertices G d).erase a} ∣
      LinearMap.charpoly (G.adjMatrix ℚ).toLin' := by
  rw [← squareOrder_highQuadraticSector_restrict_charpoly
    G hfree hd hmin hcover hcard ha]
  exact restrict_charpoly_dvd_charpoly (G.adjMatrix ℚ).toLin'
    (Submodule.span ℚ
      (Set.range (squareOrderHighQuadraticSectorFamily
        G (squareOrderHighVertices G d) a)))
    (squareOrder_highQuadraticSector_span_invariant
      G hfree hd hmin hcard ha)

/-- Cardinality-normalized form of the high-sector factor: its exponent is
exactly one less than the number of high vertices. -/
theorem squareOrder_highQuadraticFactor_card_sub_one_dvd_adjMatrixRat_charpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)) ^
        ((squareOrderHighVertices G d).card - 1) ∣
      LinearMap.charpoly (G.adjMatrix ℚ).toLin' := by
  have h := squareOrder_highQuadraticFactor_dvd_adjMatrixRat_charpoly
    G hfree hd hmin hcover hcard ha
  rw [Fintype.card_coe, Finset.card_erase_of_mem ha] at h
  exact h

end

end Erdos85
