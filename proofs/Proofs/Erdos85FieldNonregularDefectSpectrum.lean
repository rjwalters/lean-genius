import Proofs.Erdos85NonregularDefectOperator

/-!
# Field-valued nonregular defect spectrum

The integral nonregular identity

`A² = Delta + J - D`

is transported to an arbitrary commutative ring.  This supplies the
degree-band adjacency/defect spectral pairing over fields containing
non-rational eigenvalues, without adding a regularity hypothesis.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The all-ones matrix over an arbitrary scalar ring. -/
def onesMatrixOver (K V : Type*) [One K] : Matrix V V K :=
  Matrix.of fun _ _ ↦ 1

/-- The degree-predecessor diagonal over an arbitrary scalar ring. -/
def degreePredDiagonalOver
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V K :=
  Matrix.diagonal fun x ↦ (G.degree x : K) - 1

/-- Casting the integral adjacency matrix gives the adjacency matrix over
the target commutative ring. -/
theorem adjMatrix_intCast_map
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℤ).map (Int.castRingHom K) = G.adjMatrix K := by
  ext x y
  simp [SimpleGraph.adjMatrix_apply]

/-- Casting the integral all-ones matrix gives `onesMatrixOver`. -/
theorem onesMatrix_intCast_map
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V] :
    (FriendshipTheoremOQ01.onesMatrix V).map (Int.castRingHom K) =
      onesMatrixOver K V := by
  ext x y
  simp [FriendshipTheoremOQ01.onesMatrix, onesMatrixOver]

/-- Casting the integral degree-predecessor diagonal gives its
ring-valued form. -/
theorem degreePredDiagonal_intCast_map
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (degreePredDiagonal G).map (Int.castRingHom K) =
      degreePredDiagonalOver (K := K) G := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [degreePredDiagonal, degreePredDiagonalOver]
  · simp [degreePredDiagonal, degreePredDiagonalOver, hxy]

/-- **Field-generic nonregular defect identity.**  In fact no field or
characteristic-zero hypothesis is needed: the identity holds over every
commutative ring. -/
theorem c4Free_adjMatrix_sq_eq_degreePredDiagonalOver_add_ones_sub_defect
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    G.adjMatrix K * G.adjMatrix K =
      degreePredDiagonalOver (K := K) G + onesMatrixOver K V -
        (secondOrderDefectGraph G).adjMatrix K := by
  have h := congrArg (fun M ↦ M.map (Int.castRingHom K))
    (adjMatrix_sq_eq_degreePredDiagonal_add_ones_sub_secondOrderDefect
      G hfree)
  rw [Matrix.map_mul,
    Matrix.map_sub (Int.castRingHom K) (Int.castRingHom K).map_sub,
    Matrix.map_add (Int.castRingHom K) (Int.castRingHom K).map_add] at h
  rw [adjMatrix_intCast_map, degreePredDiagonal_intCast_map,
    onesMatrix_intCast_map,
    adjMatrix_intCast_map (K := K) (secondOrderDefectGraph G)] at h
  exact h

/-- A vector supported on one degree band is an eigenvector of the
ring-valued degree-predecessor diagonal. -/
theorem degreePredDiagonalOver_mulVec_of_support_degree
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → K) {d : ℕ}
    (hsupport : ∀ x, f x ≠ 0 → G.degree x = d) :
    (degreePredDiagonalOver G).mulVec f = ((d : K) - 1) • f := by
  funext x
  by_cases hx : f x = 0
  · simp [degreePredDiagonalOver, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply, hx]
  · have hdx : G.degree x = d := hsupport x hx
    simp [degreePredDiagonalOver, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply, hdx]

/-- **Global field-valued nonregular spectral pairing.**  A zero-sum
adjacency eigenvector which is also a degree-diagonal eigenvector is a
defect eigenvector with eigenvalue `delta - theta²`. -/
theorem c4Free_secondOrderDefect_mulVec_of_adj_degreeEigenvector_over
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (f : V → K) (theta delta : K)
    (hsum : ∑ x, f x = 0)
    (hA : (G.adjMatrix K).mulVec f = theta • f)
    (hDelta : (degreePredDiagonalOver G).mulVec f = delta • f) :
    ((secondOrderDefectGraph G).adjMatrix K).mulVec f =
      (delta - theta ^ 2) • f := by
  let A := G.adjMatrix K
  let D := (secondOrderDefectGraph G).adjMatrix K
  let Delta := degreePredDiagonalOver (K := K) G
  let J := onesMatrixOver K V
  have hsq : A * A = Delta + J - D := by
    simpa [A, D, Delta, J] using
      c4Free_adjMatrix_sq_eq_degreePredDiagonalOver_add_ones_sub_defect
        (K := K) G hfree
  have hJzero : J.mulVec f = 0 := by
    funext x
    simp [J, onesMatrixOver, Matrix.mulVec, dotProduct, hsum]
  have hv := congrArg (fun M : Matrix V V K ↦ M.mulVec f) hsq
  change D.mulVec f = (delta - theta ^ 2) • f
  change A.mulVec f = theta • f at hA
  change Delta.mulVec f = delta • f at hDelta
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    hA, Matrix.mulVec_smul, hA, hDelta, hJzero] at hv
  ext x
  have hx := congrFun hv x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at hx ⊢
  ring_nf at hx ⊢
  linear_combination hx

/-- Support-degree form of the field-valued global pairing. -/
theorem c4Free_secondOrderDefect_mulVec_of_adj_eigenvector_supported_on_degree_over
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (f : V → K) (theta : K) {d : ℕ}
    (hsum : ∑ x, f x = 0)
    (hA : (G.adjMatrix K).mulVec f = theta • f)
    (hsupport : ∀ x, f x ≠ 0 → G.degree x = d) :
    ((secondOrderDefectGraph G).adjMatrix K).mulVec f =
      (((d : K) - 1) - theta ^ 2) • f := by
  exact c4Free_secondOrderDefect_mulVec_of_adj_degreeEigenvector_over
    G hfree f theta ((d : K) - 1) hsum hA
      (degreePredDiagonalOver_mulVec_of_support_degree G f hsupport)

end

end Erdos85

#print axioms Erdos85.adjMatrix_intCast_map
#print axioms
  Erdos85.c4Free_adjMatrix_sq_eq_degreePredDiagonalOver_add_ones_sub_defect
#print axioms
  Erdos85.c4Free_secondOrderDefect_mulVec_of_adj_degreeEigenvector_over
#print axioms
  Erdos85.c4Free_secondOrderDefect_mulVec_of_adj_eigenvector_supported_on_degree_over
