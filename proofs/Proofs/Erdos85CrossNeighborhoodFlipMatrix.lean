import Proofs.Erdos85CrossNeighborhoodMatching

/-!
# Cross-neighborhood flip parity as a matrix commutator

The endpoint-weighted parity of the full cross-neighborhood matching is the
nonlinear matrix expression in `(73rnz_cjibky)`.  For a Boolean shore
indicator, the weight is one exactly on edges whose endpoint labels differ.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Boolean endpoint labels which differ across a cross-neighborhood edge. -/
def crossNeighborhoodFlipEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (E G : V) (B : Finset V) :
    Finset (V × V) :=
  (crossNeighborhoodEdgeFinset A E G).filter
    (fun e => (e.1 ∈ B) ≠ (e.2 ∈ B))

/-- The weighted cross-neighborhood edge sum is the adjacency commutator
`A diag(b) A² + A² diag(b) A`, evaluated at the two roots. -/
theorem crossNeighborhood_endpointWeight_sum_eq_matrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (b : V → ZMod 2) (E G : V) :
    ∑ e ∈ crossNeighborhoodEdgeFinset A E G, (b e.1 + b e.2) =
      (A.adjMatrix (ZMod 2) * Matrix.diagonal b *
          (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2)) +
        (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2)) *
          Matrix.diagonal b * A.adjMatrix (ZMod 2)) E G := by
  classical
  have hneighbor (v : V) :
      A.neighborFinset v = Finset.univ.filter (A.Adj v) := by
    ext x
    simp [SimpleGraph.mem_neighborFinset]
  simp only [crossNeighborhoodEdgeFinset, Finset.sum_filter,
    Finset.sum_product]
  rw [hneighbor E, Finset.sum_filter]
  simp_rw [hneighbor G, Finset.sum_filter]
  rw [Matrix.add_apply]
  conv_rhs =>
    lhs
    rw [Matrix.mul_apply]
  conv_rhs =>
    rhs
    rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]
  simp_rw [Matrix.mul_apply]
  simp only [SimpleGraph.adjMatrix_apply, ite_mul, mul_ite, one_mul,
    zero_mul, mul_one]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero]
  simp only [Finset.sum_const_zero]
  simp only [A.adj_comm]
  have hsecond :
      (∑ y, if A.Adj G y then
          ∑ x, if A.Adj y x then if A.Adj E x then b y else 0 else 0
        else 0) =
      ∑ x, ∑ y, if A.Adj E x then
        if A.Adj G y then if A.Adj x y then b y else 0 else 0 else 0 := by
    calc
      _ = ∑ y, ∑ x, if A.Adj E x then
          if A.Adj G y then if A.Adj x y then b y else 0 else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hG : A.Adj G y
        · simp only [hG, if_true]
          apply Finset.sum_congr rfl
          intro x _
          have hyx : A.Adj y x ↔ A.Adj x y := A.adj_comm y x
          by_cases hE : A.Adj E x <;> by_cases hxy : A.Adj x y <;>
            simp [hE, hxy, hyx]
        · simp [hG]
      _ = _ := Finset.sum_comm
  simp only [ite_self]
  rw [hsecond, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : A.Adj E x
  · simp only [hx, if_true, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : A.Adj G y <;> by_cases hxy : A.Adj x y <;>
      simp [hy, hxy]
  · simp [hx]

/-- For a finset indicator, the endpoint weight is one exactly on flip edges
and zero on same-side edges; hence the commutator is the flip cardinality
modulo two. -/
theorem crossNeighborhoodFlipEdgeFinset_card_cast_eq_matrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (E G : V) (B : Finset V) :
    let b : V → ZMod 2 := fun v => if v ∈ B then 1 else 0
    ((crossNeighborhoodFlipEdgeFinset A E G B).card : ZMod 2) =
      (A.adjMatrix (ZMod 2) * Matrix.diagonal b *
          (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2)) +
        (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2)) *
          Matrix.diagonal b * A.adjMatrix (ZMod 2)) E G := by
  classical
  dsimp only
  rw [← crossNeighborhood_endpointWeight_sum_eq_matrix]
  simp only [crossNeighborhoodFlipEdgeFinset]
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro e he
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases h₁ : e.1 ∈ B <;> by_cases h₂ : e.2 ∈ B <;>
    simp [h₁, h₂, hone]

end

end Erdos85

#print axioms Erdos85.crossNeighborhood_endpointWeight_sum_eq_matrix
#print axioms Erdos85.crossNeighborhoodFlipEdgeFinset_card_cast_eq_matrix
