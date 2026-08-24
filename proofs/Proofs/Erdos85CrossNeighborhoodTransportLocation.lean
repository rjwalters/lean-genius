import Proofs.Erdos85OrdinaryResidualNuMuDecomposition
import Proofs.Erdos85CrossNeighborhoodMatching

/-!
# Locating the binary transport by cross-neighborhood matchings

For nonadjacent roots, a length-three ambient walk is exactly an oriented
edge between their two neighborhoods.  Thus the cubic entry in the binary
transport is not merely a matrix coefficient: it is the parity of the
cross-neighborhood partial matching.  Combining this count with the
quadratic common-neighbor atom gives the graph-facing form of equation (21)
in the Baer involution audit.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The cubic adjacency entry is the cardinality modulo two of the oriented
cross-neighborhood edge set. -/
theorem crossNeighborhoodEdgeFinset_card_cast_eq_adjMatrix_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (u v : V) :
    ((crossNeighborhoodEdgeFinset A u v).card : ZMod 2) =
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
        A.adjMatrix (ZMod 2)) u v := by
  classical
  rw [show ((crossNeighborhoodEdgeFinset A u v).card : ZMod 2) =
      ∑ e ∈ crossNeighborhoodEdgeFinset A u v, (1 : ZMod 2) by simp]
  simp only [crossNeighborhoodEdgeFinset, Finset.sum_filter,
    Finset.sum_product]
  calc
    (∑ a ∈ A.neighborFinset u, ∑ b ∈ A.neighborFinset v,
        if A.Adj a b then 1 else 0) =
        ∑ b ∈ A.neighborFinset v, ∑ a ∈ A.neighborFinset u,
          if A.Adj a b then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
          A.adjMatrix (ZMod 2)) u v := by
      rw [Matrix.mul_apply]
      simp only [SimpleGraph.adjMatrix_apply, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      have hvfilter :
          (Finset.univ.filter fun b ↦ A.Adj b v) = A.neighborFinset v := by
        ext b
        simp [SimpleGraph.mem_neighborFinset, A.adj_comm]
      rw [hvfilter]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Matrix.mul_apply]
      simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
      rw [show (∑ x, if A.Adj u x then if A.Adj x b then (1 : ZMod 2) else 0 else 0) =
          ∑ x ∈ (A.neighborFinset u).filter (fun x ↦ A.Adj x b), (1 : ZMod 2) by
        have hufilter :
            (Finset.univ.filter fun x ↦ A.Adj u x) = A.neighborFinset u := by
          ext x
          simp [SimpleGraph.mem_neighborFinset]
        rw [← Finset.sum_filter, hufilter, ← Finset.sum_filter]]
      simp

/-- **Nonlinear transport-location identity (Baer audit (21)).**  On a
non-ambient pair, `K`-adjacency is the xor of the common-neighbor atom and
the parity of the cross-neighborhood partial matching. -/
theorem binaryTransportResidualGraph_adj_iff_common_add_cross_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    {u v : V} (hnotA : ¬ A.Adj u v) :
    (binaryTransportResidualGraph A hq hreg).Adj u v ↔
      (((A.neighborFinset u ∩ A.neighborFinset v).card : ℕ) : ZMod 2) +
        ((crossNeighborhoodEdgeFinset A u v).card : ZMod 2) = 1 := by
  rw [← graphEdgeIndicator_eq_one_iff]
  rw [graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_of_not_adj
    A hq hreg hnotA]
  rw [crossNeighborhoodEdgeFinset_card_cast_eq_adjMatrix_cube]

/-- On a zero-common-neighbor pair (in particular, on a defect edge), the
canonical residual transport is present exactly when the cross-neighborhood
matching has odd cardinality. -/
theorem binaryTransportResidualGraph_adj_iff_cross_odd_of_common_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    {u v : V} (hnotA : ¬ A.Adj u v)
    (hcommon : (A.neighborFinset u ∩ A.neighborFinset v).card = 0) :
    (binaryTransportResidualGraph A hq hreg).Adj u v ↔
      ((crossNeighborhoodEdgeFinset A u v).card : ZMod 2) = 1 := by
  rw [binaryTransportResidualGraph_adj_iff_common_add_cross_odd
    A hq hreg hnotA, hcommon]
  simp

/-- The defect-edge half of audit equation (21): on a non-ambient defect
pair, `K` records precisely odd cross-neighborhood matching size. -/
theorem binaryTransportResidualGraph_adj_iff_cross_odd_of_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (antipodalGraph A).Adj]
    (hfree : ¬ containsC4 V A)
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    {u v : V} (hnotA : ¬ A.Adj u v)
    (hD : (secondOrderDefectGraph A).Adj u v) :
    (binaryTransportResidualGraph A hq hreg).Adj u v ↔
      ((crossNeighborhoodEdgeFinset A u v).card : ZMod 2) = 1 := by
  apply binaryTransportResidualGraph_adj_iff_cross_odd_of_common_zero
    A hq hreg hnotA
  exact (secondOrderDefectGraph_adj_iff_card_common_eq_zero
    A hfree hD.ne).mp hD

/-- On a unique-common-neighbor nonedge, the residual transport is present
exactly when the cross-neighborhood matching has even cardinality. -/
theorem binaryTransportResidualGraph_adj_iff_cross_even_of_common_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    {u v : V} (hnotA : ¬ A.Adj u v)
    (hcommon : (A.neighborFinset u ∩ A.neighborFinset v).card = 1) :
    (binaryTransportResidualGraph A hq hreg).Adj u v ↔
      ((crossNeighborhoodEdgeFinset A u v).card : ZMod 2) = 0 := by
  rw [binaryTransportResidualGraph_adj_iff_common_add_cross_odd
    A hq hreg hnotA, hcommon]
  constructor <;> intro h
  · have := congrArg (fun z : ZMod 2 => z + 1) h
    simpa using this
  · simp [h]

end

end Erdos85

#print axioms Erdos85.crossNeighborhoodEdgeFinset_card_cast_eq_adjMatrix_cube
#print axioms Erdos85.binaryTransportResidualGraph_adj_iff_common_add_cross_odd
#print axioms Erdos85.binaryTransportResidualGraph_adj_iff_cross_odd_of_common_zero
#print axioms Erdos85.binaryTransportResidualGraph_adj_iff_cross_odd_of_defect
#print axioms Erdos85.binaryTransportResidualGraph_adj_iff_cross_even_of_common_one
