import Proofs.Erdos85OrderSixtyFourDisconnectedDefect
import Mathlib.NumberTheory.PythagoreanTriples

/-! # Arithmetic payoff of the order-64 cofactor bridge -/

open SimpleGraph

namespace Erdos85

/-- If `a² = 64² q` over the integers, then `q` is an integer square.
The key integral step is that divisibility of the squares forces
`64 ∣ a`. -/
theorem isSquare_of_sq_eq_sixtyFour_sq_mul
    (a q : ℤ) (h : a ^ 2 = (64 : ℤ) ^ 2 * q) :
    IsSquare q := by
  have hpow : (64 : ℤ) ^ 2 ∣ a ^ 2 := by
    exact ⟨q, h⟩
  have hdiv : (64 : ℤ) ∣ a :=
    (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
  obtain ⟨b, rfl⟩ := hdiv
  refine ⟨b, ?_⟩
  nlinarith

/-- Once the rank-one defect determinant has been identified as
`64² q` (in particular when `q` is a common Laplacian cofactor), the
adjacency square identity forces `q` to be a square. -/
theorem orderSixtyFour_defect_rank_one_quotient_isSquare
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (q : ℤ)
    (hq :
      Matrix.det
        ((7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) +
          FriendshipTheoremOQ01.onesMatrix (Fin 64) -
            (secondOrderDefectGraph G).adjMatrix ℤ) =
        (64 : ℤ) ^ 2 * q) :
    IsSquare q := by
  apply isSquare_of_sq_eq_sixtyFour_sq_mul
    (Matrix.det (G.adjMatrix ℤ)) q
  rw [orderSixtyFour_adj_det_sq_eq_defect_rank_one_det
    G hfree hmin hcover]
  exact hq

end Erdos85
