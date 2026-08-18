import Proofs.Erdos85BinarySquareCenteredGlobalRank
import Proofs.Erdos85PositiveExcessQuotientTrace

/-!
# Rank of the global centered adjacency operator

Concatenating the component incidence blocks recovers the adjacency matrix.
Globally, centering therefore produces `qA-J`.  Its Gram is `q²` times the
defect Laplacian, so its rank is the square order minus the number of defect
components.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The global real centered adjacency operator `qA-J`. -/
def binarySquareCenteredAdjacencyMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) : Matrix V V ℝ :=
  (q : ℝ) • G.adjMatrix ℝ - realOnesMatrix V

private theorem binarySquare_defect_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (x : V) :
    (secondOrderDefectGraph G).degree x = q - 1 := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have h := secondOrderDefectGraph_degree_eq_excess_add_two
    G hfree hreg hcensus x
  omega

/-- At square order, the real defect Laplacian is `(q-1)I-D`. -/
theorem binarySquare_regular_defect_lapMatrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    (secondOrderDefectGraph G).lapMatrix ℝ =
      ((q - 1 : ℕ) : ℝ) • (1 : Matrix V V ℝ) -
        (secondOrderDefectGraph G).adjMatrix ℝ := by
  let D := secondOrderDefectGraph G
  ext x y
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    Matrix.sub_apply, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    simp [binarySquare_defect_degree G hfree hq hreg hcard x]
  · simp [hxy]

/-- **Global centered Gram identity.** -/
theorem transpose_binarySquareCenteredAdjacencyMatrix_mul_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    (binarySquareCenteredAdjacencyMatrix G q).transpose *
        binarySquareCenteredAdjacencyMatrix G q =
      ((q * q : ℕ) : ℝ) • (secondOrderDefectGraph G).lapMatrix ℝ := by
  let A := G.adjMatrix ℝ
  let J := realOnesMatrix V
  let D := secondOrderDefectGraph G
  have hAT : A.transpose = A := G.isSymm_adjMatrix.eq
  have hJT : J.transpose = J := by
    ext x y
    simp [J, realOnesMatrix]
  have hAJ : A * J = (q : ℝ) • J := by
    ext x y
    rw [Matrix.mul_apply]
    have hrow : A.mulVec (Function.const V 1) x = (q : ℝ) := by
      change (G.adjMatrix ℝ).mulVec (Function.const V 1) x = (q : ℝ)
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg x]
    rw [Matrix.mulVec, dotProduct] at hrow
    simpa [A, J, realOnesMatrix] using hrow
  have hJA : J * A = (q : ℝ) • J := by
    calc
      J * A = (A * J).transpose := by rw [Matrix.transpose_mul, hAT, hJT]
      _ = ((q : ℝ) • J).transpose := congrArg Matrix.transpose hAJ
      _ = (q : ℝ) • J := by rw [Matrix.transpose_smul, hJT]
  have hJJ : J * J = ((q * q : ℕ) : ℝ) • J := by
    ext x y
    simp [J, realOnesMatrix, Matrix.mul_apply, hcard]
  have hA2 : A * A =
      ((q - 1 : ℕ) : ℝ) • (1 : Matrix V V ℝ) + J - D.adjMatrix ℝ := by
    have h := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_real
      G hfree hreg
    simpa [A, J, D, Nat.cast_sub (by omega : 1 ≤ q)] using h
  have hL : D.lapMatrix ℝ =
      ((q - 1 : ℕ) : ℝ) • (1 : Matrix V V ℝ) - D.adjMatrix ℝ := by
    simpa [D] using binarySquare_regular_defect_lapMatrix_eq
      G hfree hq hreg hcard
  rw [binarySquareCenteredAdjacencyMatrix, Matrix.transpose_sub,
    Matrix.transpose_smul, hAT, hJT]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub, smul_smul]
  rw [hA2, hAJ, hJA, hJJ, hL]
  module

/-- **Exact global centered rank.**  Centering the adjacency operator loses
one dimension for every defect component and no others. -/
theorem binarySquareCenteredAdjacencyMatrix_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    (binarySquareCenteredAdjacencyMatrix G q).rank =
      q * q - Fintype.card (secondOrderDefectGraph G).ConnectedComponent := by
  let C := binarySquareCenteredAdjacencyMatrix G q
  let D := secondOrderDefectGraph G
  let L := D.lapMatrix ℝ
  have hgram : C.transpose * C = ((q * q : ℕ) : ℝ) • L := by
    simpa [C, D, L] using
      transpose_binarySquareCenteredAdjacencyMatrix_mul_self
        G hfree hq hreg hcard
  have ha : ((q * q : ℕ) : ℝ) ≠ 0 := by positivity
  have hmulVecLin :
      (((q * q : ℕ) : ℝ) • L).mulVecLin =
        ((q * q : ℕ) : ℝ) • L.mulVecLin := by
    ext v x
    simp
  have hker : Module.finrank ℝ (LinearMap.ker C.mulVecLin) =
      Fintype.card D.ConnectedComponent := by
    rw [← Matrix.ker_mulVecLin_transpose_mul_self C, hgram, hmulVecLin,
      LinearMap.ker_smul _ _ ha]
    exact D.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix.symm
  have hrankNull := LinearMap.finrank_range_add_finrank_ker C.mulVecLin
  change Module.finrank ℝ (LinearMap.range C.mulVecLin) =
    q * q - Fintype.card D.ConnectedComponent
  rw [hker] at hrankNull
  have hcardfun : Module.finrank ℝ (V → ℝ) = Fintype.card V :=
    Module.finrank_fintype_fun_eq_card ℝ
  rw [hcardfun, hcard] at hrankNull
  omega

end

end Erdos85
