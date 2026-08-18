import Proofs.Erdos85BinarySquareComponentIncidenceGram
import Proofs.Erdos85ComponentFactorization

/-!
# The stacked component-incidence matrix

Putting the component-neighbor incidence matrices side by side does not
create a new matrix: under the canonical partition of the defect vertices
into connected components, it is exactly the ambient adjacency matrix with
its columns reindexed.  Consequently its full Gram matrix is just the
similarly reindexed square of the ambient adjacency matrix.

This observation is useful as an audit boundary.  Positivity, rank, or trace
identities applied only to this full Gram matrix cannot by themselves add
information beyond the already available ambient adjacency-square identity.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- All component-neighbor incidence blocks, stacked along their common
ambient row coordinate. -/
def stackedDefectComponentNeighborIncidenceMatrix
    {K V : Type*} [Fintype V] [DecidableEq V] [Zero K] [One K]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V (Σ c : (secondOrderDefectGraph G).ConnectedComponent, c.supp) K :=
  fun x z => defectComponentNeighborIncidenceMatrix (K := K) G z.1 x z.2

/-- The stacked incidence matrix is the ambient adjacency matrix with its
column coordinate partitioned into defect components. -/
theorem stackedDefectComponentNeighborIncidenceMatrix_eq_adjMatrix_reindexed
    {K V : Type*} [Fintype V] [DecidableEq V] [Zero K] [One K]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    stackedDefectComponentNeighborIncidenceMatrix (K := K) G =
      fun x z => G.adjMatrix K x
        ((vertexConnectedComponentEquiv (secondOrderDefectGraph G)).symm z) := by
  ext x z
  rcases z with ⟨c, y⟩
  simp [stackedDefectComponentNeighborIncidenceMatrix,
    defectComponentNeighborIncidenceMatrix, vertexConnectedComponentEquiv,
    SimpleGraph.adjMatrix_apply]

/-- The full Gram of all component-incidence blocks is merely the ambient
adjacency square, reindexed by the canonical component partition. -/
theorem transpose_stackedDefectComponentNeighborIncidenceMatrix_mul_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (stackedDefectComponentNeighborIncidenceMatrix (K := ℤ) G).transpose *
        stackedDefectComponentNeighborIncidenceMatrix (K := ℤ) G =
      (G.adjMatrix ℤ * G.adjMatrix ℤ).reindex
        (vertexConnectedComponentEquiv (secondOrderDefectGraph G))
        (vertexConnectedComponentEquiv (secondOrderDefectGraph G)) := by
  ext z w
  rcases z with ⟨c, y⟩
  rcases w with ⟨d, t⟩
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.reindex_apply]
  apply Finset.sum_congr rfl
  intro x _hx
  simp [stackedDefectComponentNeighborIncidenceMatrix,
    defectComponentNeighborIncidenceMatrix, vertexConnectedComponentEquiv,
    SimpleGraph.adjMatrix_apply, G.adj_comm]

end

end Erdos85
