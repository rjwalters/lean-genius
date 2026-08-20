import Proofs.Erdos85RegularCubicRowExcessLedger
import Proofs.Erdos85SymmetricCubeTraceSquares

/-! # Arbitrary-parameter global cubic excess ledger

Node: F.3 GENERALIZATION.  Summing the arbitrary-center row identity gives
the full sixth adjacency moment without fixing the degree, order, or
histogram center.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Exact global sixth-trace ledger for a C4-free `d`-regular graph, with the
nonneighbor histogram centered at arbitrary consecutive integers `c,c+1`. -/
theorem regular_c4Free_trace_pow_six_eq_global_excess_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (c : ℤ) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    Matrix.trace ((G.adjMatrix ℤ) ^ 6) =
      ∑ a,
        ((d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
          (2 * c + 1) *
            ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
          c * (c + 1) * ((cubicNonneighborFinset G a).card : ℤ) +
          ∑ b ∈ cubicNonneighborFinset G a,
            (A3 a b - c) * (A3 a b - (c + 1))) := by
  classical
  dsimp only
  let A := G.adjMatrix ℤ
  have hA : A.IsSymm := by
    simpa [A] using (SimpleGraph.isSymm_adjMatrix G ℤ)
  rw [trace_pow_six_eq_sum_cube_apply_sq A hA]
  apply Finset.sum_congr rfl
  intro a _
  have hrow := regular_c4Free_cube_row_square_eq_baseline_add_excess
    G hfree d hreg c a
  simpa [A, pow_succ, Matrix.mul_assoc] using hrow

end


end Erdos85

#print axioms Erdos85.regular_c4Free_trace_pow_six_eq_global_excess_ledger
