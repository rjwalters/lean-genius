import Proofs.Erdos85CrossWitnessNuMuConservation

/-!
# Exact triangle correction for cross-witness nu/mu conservation

The ordinary-pair conservation theorem assumes the cut has no ambient
`A`-edge.  Without that assumption there is an exact correction: the binary
residual graph is the symmetric difference of the binary transport support
and the triangle-free-edge graph `T`.  Thus across every cut

`K-cut = (nu+mu)-mass + T-cut`.

This replaces the separation hypothesis by an explicit graph-native term.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Pointwise residual decomposition on an arbitrary pair, including the
triangle-free-edge correction which vanishes on non-`A` pairs. -/
theorem graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_add_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (u v : V) :
    graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) u v =
      (((A.neighborFinset u ∩ A.neighborFinset v).card : ℕ) : ZMod 2) +
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
        A.adjMatrix (ZMod 2)) u v +
      graphEdgeIndicator (triangleFreeEdgeGraph A) u v := by
  let H := binaryTransportSupportGraph A hq hreg
  let T := triangleFreeEdgeGraph A
  have hKmatrix :
      (binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2) =
        H.adjMatrix (ZMod 2) + T.adjMatrix (ZMod 2) := by
    unfold binaryTransportResidualGraph graphF2SymmetricDifference
    exact f2MatrixSupportGraph_adjMatrix_eq _ _ _
  have hHmatrix : H.adjMatrix (ZMod 2) = binaryTransportMatrix A :=
    f2MatrixSupportGraph_adjMatrix_eq _ _ _
  calc
    graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) u v =
        (binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2) u v := by
      simp [graphEdgeIndicator, SimpleGraph.adjMatrix_apply]
    _ = H.adjMatrix (ZMod 2) u v + T.adjMatrix (ZMod 2) u v := by
      rw [hKmatrix, Matrix.add_apply]
    _ = binaryTransportMatrix A u v + T.adjMatrix (ZMod 2) u v := by
      rw [hHmatrix]
    _ = (((A.adjMatrix (ZMod 2)) ^ 3 +
          (A.adjMatrix (ZMod 2)) ^ 2) u v) +
          T.adjMatrix (ZMod 2) u v := by
      rw [binaryTransportMatrix_eq_cube_add_sq]
    _ = (((A.neighborFinset u ∩ A.neighborFinset v).card : ℕ) : ZMod 2) +
        (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
          A.adjMatrix (ZMod 2)) u v +
        graphEdgeIndicator T u v := by
      rw [Matrix.add_apply]
      rw [show (A.adjMatrix (ZMod 2)) ^ 2 =
          A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) by simp [pow_two]]
      rw [show (A.adjMatrix (ZMod 2)) ^ 3 =
          A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
            A.adjMatrix (ZMod 2) by simp [pow_succ, mul_assoc]]
      rw [adjMatrix_sq_apply_eq_card_common_zmodTwo]
      simp [graphEdgeIndicator, SimpleGraph.adjMatrix_apply, add_comm]

/-- Cut mass is the double sum of edge indicators from the set to its
complement. -/
theorem graphCutMass_cast_eq_sum_indicator_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V) :
    (graphCutMass G R : ZMod 2) =
      ∑ y ∈ R, ∑ z ∈ ordinaryWitnessComplement R,
        graphEdgeIndicator G y z := by
  unfold graphCutMass
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  rw [sum_graphEdgeIndicator_eq_neighbor_inter_card_cast]
  rw [neighbor_inter_ordinaryWitnessComplement]

/-- **Exact cross-witness conservation (`73rnz_cjibkzm`).**  Residual
character one equals ordinary `nu+mu` mass plus the explicit triangle-edge
cut correction, with no ambient separation assumption. -/
theorem sum_ordinaryResidualNuMuMass_add_triangleCut_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (R : Finset V)
    (hcharacter :
      (∑ y ∈ R,
        ((binaryTransportResidualGraph A hq hreg).degree y : ZMod 2)) = 1) :
    (∑ y ∈ R,
      ordinaryResidualNuMuMass A y (ordinaryWitnessComplement R)) +
      (graphCutMass (triangleFreeEdgeGraph A) R : ZMod 2) = 1 := by
  let K := binaryTransportResidualGraph A hq hreg
  let T := triangleFreeEdgeGraph A
  have hcutK : (graphCutMass K R : ZMod 2) = 1 := by
    rw [← degreeParity_sum_eq_graphCutMass_cast K R]
    exact hcharacter
  rw [graphCutMass_cast_eq_sum_indicator_complement T R]
  rw [graphCutMass_cast_eq_sum_indicator_complement K R] at hcutK
  rw [← hcutK]
  unfold ordinaryResidualNuMuMass
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  exact (graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_add_triangle
    A hq hreg y z).symm

end


end Erdos85

#print axioms Erdos85.graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_add_triangle
#print axioms Erdos85.graphCutMass_cast_eq_sum_indicator_complement
#print axioms Erdos85.sum_ordinaryResidualNuMuMass_add_triangleCut_eq_one
