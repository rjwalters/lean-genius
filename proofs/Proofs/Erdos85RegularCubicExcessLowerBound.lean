import Proofs.Erdos85RegularCubicGlobalExcessLedger

/-! # Nonnegative arbitrary-center cubic excess bounds

Node: F.3 GENERALIZATION.  Consecutive integer centers make every histogram
correction nonnegative, turning the exact row and global ledgers into usable
sixth-moment lower bounds.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- An integer cannot lie strictly between consecutive integers, so the
associated quadratic correction is nonnegative. -/
theorem consecutive_integer_excess_nonneg (x c : ℤ) :
    0 ≤ (x - c) * (x - (c + 1)) := by
  by_cases hx : x ≤ c
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

/-- Rowwise sixth-moment lower bound obtained by discarding the nonnegative
arbitrary-center histogram correction. -/
theorem regular_c4Free_cube_row_square_baseline_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (c : ℤ) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    let Q := cubicNonneighborFinset G a
    (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
        (2 * c + 1) *
          ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
        c * (c + 1) * (Q.card : ℤ) ≤
      ∑ b, (A3 a b) ^ 2 := by
  classical
  dsimp only
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let Q := cubicNonneighborFinset G a
  have hexcess : 0 ≤ ∑ b ∈ Q,
      (A3 a b - c) * (A3 a b - (c + 1)) := by
    apply Finset.sum_nonneg
    intro b _
    exact consecutive_integer_excess_nonneg (A3 a b) c
  have hledger := regular_c4Free_cube_row_square_eq_baseline_add_excess
    G hfree d hreg c a
  change (∑ b, (A3 a b) ^ 2) =
    (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
      (2 * c + 1) *
        ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
      c * (c + 1) * (Q.card : ℤ) +
      ∑ b ∈ Q, (A3 a b - c) * (A3 a b - (c + 1)) at hledger
  have hlocal :
      (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
          (2 * c + 1) *
            ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
          c * (c + 1) * (Q.card : ℤ) ≤
        ∑ b, (A3 a b) ^ 2 := by
    rw [hledger]
    omega
  simpa only [A3, Q] using hlocal

/-- Global sixth-moment lower bound, retaining the diagonal cubic entries and
the exact nonneighbor-sector cardinality in every row. -/
theorem regular_c4Free_global_baseline_le_trace_pow_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (c : ℤ) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    (∑ a,
      ((d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
        (2 * c + 1) *
          ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
        c * (c + 1) * ((cubicNonneighborFinset G a).card : ℤ))) ≤
      Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  classical
  dsimp only
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  have hrows : (∑ a,
      ((d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
        (2 * c + 1) *
          ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
        c * (c + 1) * ((cubicNonneighborFinset G a).card : ℤ))) ≤
      ∑ a, ∑ b, (A3 a b) ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    exact regular_c4Free_cube_row_square_baseline_le
      G hfree d hreg c a
  let A := G.adjMatrix ℤ
  have hA : A.IsSymm := by
    simpa [A] using (SimpleGraph.isSymm_adjMatrix G ℤ)
  have htrace : (∑ a, ∑ b, (A3 a b) ^ 2) =
      Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
    have hcube : A ^ 3 = A * A * A := by
      simp [pow_succ, Matrix.mul_assoc]
    symm
    rw [trace_pow_six_eq_sum_cube_apply_sq A hA, hcube]
  rw [htrace] at hrows
  exact hrows

end


end Erdos85

#print axioms Erdos85.consecutive_integer_excess_nonneg
#print axioms Erdos85.regular_c4Free_cube_row_square_baseline_le
#print axioms Erdos85.regular_c4Free_global_baseline_le_trace_pow_six
