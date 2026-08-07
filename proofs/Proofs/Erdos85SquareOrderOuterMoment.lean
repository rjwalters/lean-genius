import Proofs.Erdos85SquareOrderOuterGraph
import Proofs.Erdos85C4FreeFourthMoment

/-!
# Fourth moment of the square-order outer graph

The outer graph is regular and `C4`-free, so its fourth adjacency moment is
completely determined.  At order 49 the 6-regular graph on 40 outer vertices
has `tr(A^4)=2640`.  This is the matrix-level compression of the branch
four-cycle holonomy constraints.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Uniform fourth moment of the induced outer graph. -/
theorem trace_squareOrderOuterGraph_fourth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hcard : Fintype.card V = d * d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = d) :
    let R := squareOrderOuterGraph G v
    Matrix.trace ((R.adjMatrix ℤ * R.adjMatrix ℤ) *
        (R.adjMatrix ℤ * R.adjMatrix ℤ)) =
      2 * (((d + 1) * (d - 2) : ℕ) : ℤ) * ((d - 1 : ℕ) : ℤ) ^ 2 -
        (((d + 1) * (d - 2) : ℕ) : ℤ) * ((d - 1 : ℕ) : ℤ) := by
  classical
  dsimp only
  rw [trace_adjMatrix_fourth_of_not_containsC4 _
    (squareOrderOuterGraph_not_containsC4 G hfree)]
  have hreg := squareOrderOuterGraph_regular
    G hfree hd hcard hv hneigh hlocal houterDegree
  simp_rw [hreg]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ,
    card_squareOrderOuterGraph G hfree hd hv hneigh hlocal]
  simp
  ring

/-- In the unique-high order-49 sector the outer fourth moment is 2640. -/
theorem orderFortyNine_trace_outerGraph_fourth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v) :
    let R := squareOrderOuterGraph G v
    Matrix.trace ((R.adjMatrix ℤ * R.adjMatrix ℤ) *
        (R.adjMatrix ℤ * R.adjMatrix ℤ)) = 2640 := by
  have hstructure := squareOrder_degree_succ_highRoot_structure
    G hfree (by omega : 2 ≤ 7) hmin (by simpa using hcard) hv
  have houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7 := by
    intro a ha
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard a with ha7 | ha8
    · exact ha7
    · have hav : a = v := hunique ha8
      rw [secondLayer] at ha
      rcases Finset.mem_biUnion.mp ha with ⟨s, _, has⟩
      exact ((Finset.mem_sdiff.mp has).2 (by simp [hav])).elim
  have hmoment := trace_squareOrderOuterGraph_fourth
    G hfree (by omega : 2 ≤ 7) (by simpa using hcard) hv
      hstructure.2.1 hstructure.2.2 houterDegree
  norm_num at hmoment ⊢
  exact hmoment

end

end Erdos85
