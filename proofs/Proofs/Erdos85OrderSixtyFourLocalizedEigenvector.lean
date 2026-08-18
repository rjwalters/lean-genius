import Proofs.Erdos85OrderSixtyFourNonlinearSupport

/-! # Restricting supported eigenvectors to the order-16 block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If a vector is supported on `s`, global adjacency at a vertex of `s`
is exactly adjacency of the induced graph applied to the restricted vector. -/
theorem adjMatrix_mulVec_eq_induce_mulVec_of_support
    {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) [Fintype s]
    (v : V → K) (hv : ∀ y, y ∉ s → v y = 0) (x : s) :
    (G.adjMatrix K).mulVec v x.1 =
      ((G.induce s).adjMatrix K).mulVec (fun y : s => v y.1) x := by
  classical
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  calc
    (∑ y : V, G.adjMatrix K x.1 y * v y) =
        ∑ y : V, if y ∈ s then G.adjMatrix K x.1 y * v y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ s
      · simp [hy]
      · simp [hy, hv y hy]
    _ = ∑ y ∈ (Finset.univ : Finset V).filter (fun y => y ∈ s),
        G.adjMatrix K x.1 y * v y := by
      rw [← Finset.sum_filter]
    _ = ∑ y : s, G.adjMatrix K x.1 y.1 * v y.1 := by
      simpa using (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset V)) (p := fun y => y ∈ s)
        (fun y => G.adjMatrix K x.1 y * v y)).symm
    _ = ∑ y : s, (G.induce s).adjMatrix K x y * v y.1 := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [SimpleGraph.adjMatrix_apply]
      rfl

/-- A nonzero global adjacency eigenvector supported on a defect component
restricts to an eigenvector of the ambient graph induced on that component. -/
theorem induce_adjMatrix_eigenvector_of_global_eigenvector_of_support
    {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) [Fintype s]
    (v : V → K) (hv : ∀ y, y ∉ s → v y = 0) (θ : K)
    (heigen : (G.adjMatrix K).mulVec v = θ • v) :
    ((G.induce s).adjMatrix K).mulVec (fun y : s => v y.1) =
      θ • (fun y : s => v y.1) := by
  funext x
  rw [← adjMatrix_mulVec_eq_induce_mulVec_of_support G s v hv x]
  exact congrFun heigen x.1

end

end Erdos85
