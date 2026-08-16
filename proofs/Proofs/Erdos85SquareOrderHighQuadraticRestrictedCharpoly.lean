import Proofs.Erdos85SquareOrderHighQuadraticCharpoly
import Proofs.Erdos85SquareOrderHighQuadraticSector
import Proofs.Erdos85InvariantCharpolyDivisibility

/-!
# Characteristic polynomial of the high quadratic sector

The natural high-difference basis makes restricted adjacency a direct sum of
exchanged two-dimensional blocks.  Its characteristic polynomial is therefore
`(X²-d)^(h-1)`.
-/

namespace Erdos85

noncomputable section

private theorem highSector_charpoly_blockDiagonal
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

private def highSectorQuadraticPairMatrix
    {R : Type*} [CommRing R] (d : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, d; 1, 0]

private theorem highSectorQuadraticPairMatrix_charpoly
    {R : Type*} [CommRing R] (d : R) :
    (highSectorQuadraticPairMatrix d).charpoly =
      Polynomial.X ^ 2 - Polynomial.C d := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  simp [highSectorQuadraticPairMatrix]
  ring

private theorem highSectorQuadraticExchangeMatrix_charpoly
    {R E : Type*} [CommRing R] [Fintype E] [DecidableEq E] (d : R) :
    (Matrix.fromBlocks (0 : Matrix E E R)
        (d • (1 : Matrix E E R)) (1 : Matrix E E R) 0).charpoly =
      (Polynomial.X ^ 2 - Polynomial.C d) ^ Fintype.card E := by
  let e : Fin 2 × E ≃ Sum E E :=
    (Equiv.prodCongr finTwoEquiv (Equiv.refl E)).trans
      (Equiv.boolProdEquivSum E)
  rw [← Matrix.charpoly_reindex e.symm]
  have hreindex :
      Matrix.reindex e.symm e.symm
          (Matrix.fromBlocks (0 : Matrix E E R)
            (d • (1 : Matrix E E R)) (1 : Matrix E E R) 0) =
        Matrix.blockDiagonal
          (fun _ : E => highSectorQuadraticPairMatrix d) := by
    have hzero : finTwoEquiv (0 : Fin 2) = false := by native_decide
    have hone : finTwoEquiv (1 : Fin 2) = true := by native_decide
    ext ⟨i, k⟩ ⟨j, l⟩
    fin_cases i <;> fin_cases j <;> by_cases hkl : k = l <;>
      simp [Matrix.reindex_apply, Matrix.blockDiagonal_apply,
        highSectorQuadraticPairMatrix, e, hkl, hzero, hone]
  rw [hreindex, highSector_charpoly_blockDiagonal]
  simp [highSectorQuadraticPairMatrix_charpoly]

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
    (LinearMap.restrict (G.adjMatrix ℚ).toLin'
      (squareOrder_highQuadraticSector_span_invariant
        G hfree hd hmin hcard ha)).charpoly =
      (Polynomial.X ^ 2 - Polynomial.C (d : ℚ)) ^
        ((squareOrderHighVertices G d).card - 1) := by
  let E := {x // x ∈ (squareOrderHighVertices G d).erase a}
  let B := squareOrderHighQuadraticSectorBasis
    G hfree hd hmin hcover hcard ha
  let T := LinearMap.restrict (G.adjMatrix ℚ).toLin'
    (squareOrder_highQuadraticSector_span_invariant
      G hfree hd hmin hcard ha)
  have hmatrix := squareOrder_highQuadraticSector_restrict_toMatrix
    G hfree hd hmin hcover hcard ha
  have hchar : T.charpoly = (LinearMap.toMatrix B B T).charpoly :=
    (LinearMap.charpoly_toMatrix T B).symm
  rw [hchar, hmatrix, highSectorQuadraticExchangeMatrix_charpoly]
  congr 1
  rw [Fintype.card_coe, Finset.card_erase_of_mem ha]

theorem squareOrder_highQuadraticSector_factor_dvd_adjMatrix_charpoly
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
      (G.adjMatrix ℚ).charpoly := by
  let U := Submodule.span ℚ
    (Set.range (squareOrderHighQuadraticSectorFamily
      G (squareOrderHighVertices G d) a))
  let T := (G.adjMatrix ℚ).toLin'
  have hdvd := charpoly_restrict_dvd_of_invariant T U
    (squareOrder_highQuadraticSector_span_invariant
      G hfree hd hmin hcard ha)
  rw [squareOrder_highQuadraticSector_restrict_charpoly
    G hfree hd hmin hcover hcard ha] at hdvd
  simpa [T, Matrix.charpoly_toLin'] using hdvd

end

end Erdos85
