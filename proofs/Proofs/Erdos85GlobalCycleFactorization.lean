import Proofs.Erdos85ComponentCycleCharpoly

namespace Erdos85

open SimpleGraph

theorem secondOrderDefect_resolvent_eq_prod_chebyshev
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree) (hcard : Fintype.card V = d * (d - 1) + 3)
    (a : ℤ) :
    ∃ r : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ c, 3 ≤ r c) ∧
      Matrix.det (Matrix.scalar V a - (secondOrderDefectGraph G).adjMatrix ℤ) =
        ∏ c, (Polynomial.Chebyshev.C ℤ (r c : ℤ) - 2).eval a := by
  classical
  choose r hr hdet using fun c =>
    secondOrderDefect_component_resolvent_chebyshev
      G hfree hd heven hmin hcard c a
  refine ⟨r, hr, ?_⟩
  rw [det_resolvent_eq_prod_connectedComponents]
  apply Finset.prod_congr rfl
  intro c hc
  have hscalar : Matrix.scalar c.supp a =
      Matrix.diagonal (fun _ : c.supp ↦ a) := rfl
  rw [hscalar, hdet c]

end Erdos85
