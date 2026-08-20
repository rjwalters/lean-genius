import Proofs.Erdos85OrderFortyNineOneHighOverlap
import Proofs.Erdos85C4FreeRegularAdjacencyCube

/-! # Parity of diagonal cubic adjacency entries -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A diagonal cubic adjacency entry is even: it counts oriented edges in
the open neighborhood of the marked vertex. -/
theorem even_adjMatrix_cube_apply_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) :
    Even ((G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a a) := by
  have hcard := card_neighborToNeighborEdgeBlock_eq_adjMatrix_cube_apply
    G a a
  have heven := even_card_neighborToNeighborEdgeBlock_self G a
  have hcast :
      (((G.adjMatrix ℕ * G.adjMatrix ℕ * G.adjMatrix ℕ) a a : ℕ) : ℤ) =
        (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a a := by
    simp only [Matrix.mul_apply, SimpleGraph.adjMatrix_apply]
    push_cast
    rfl
  rcases heven with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  rw [← hcast, ← hcard, hk]
  norm_num

/-- In the six-regular C4-free service, each diagonal cubic entry is one of
the four even values in its already-established interval `[0,6]`. -/
theorem sixRegular_c4Free_adjMatrix_cube_apply_self_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6) (a : V) :
    let q := (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a a
    q = 0 ∨ q = 2 ∨ q = 4 ∨ q = 6 := by
  dsimp only
  have hnonneg := adjMatrix_cube_apply_nonneg G a a
  have hle := c4Free_regular_adjMatrix_cube_apply_diag_le
    G hfree 6 hreg a
  have heven := even_adjMatrix_cube_apply_self G a
  rcases heven with ⟨k, hk⟩
  omega

end

end Erdos85

#print axioms Erdos85.even_adjMatrix_cube_apply_self
#print axioms Erdos85.sixRegular_c4Free_adjMatrix_cube_apply_self_cases
