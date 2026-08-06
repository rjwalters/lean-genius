import Proofs.Erdos85AlternatingFourthMoment
import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85PositiveExcessOneOperator

/-!
# The antipodal and triangle-free color commutators

If `A` commutes with `D = C + T`, then its two color commutators are
negatives:

`A C - C A = -(A T - T A)`.

Their squares, traces, and Frobenius norms therefore agree.  In the
second-order defect decomposition this gives a genuinely mixed equation:
the already-computable triangle-free side of the commutator can be matched
against the antipodal side.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Abstract color-commutator identity. -/
theorem commutator_eq_neg_of_commutes_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C T : Matrix ι ι ℤ)
    (hcomm : A * (C + T) = (C + T) * A) :
    A * C - C * A = -(A * T - T * A) := by
  rw [mul_add, add_mul] at hcomm
  rw [neg_sub]
  apply sub_eq_sub_iff_add_eq_add.mpr
  exact hcomm.trans (add_comm _ _)

/-- Squaring removes the sign in the color-commutator identity. -/
theorem commutator_sq_eq_of_commutes_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C T : Matrix ι ι ℤ)
    (hcomm : A * (C + T) = (C + T) * A) :
    (A * C - C * A) * (A * C - C * A) =
      (A * T - T * A) * (A * T - T * A) := by
  rw [commutator_eq_neg_of_commutes_add A C T hcomm]
  noncomm_ring

/-- Trace form of equality of the two commutator squares. -/
theorem trace_commutator_sq_eq_of_commutes_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C T : Matrix ι ι ℤ)
    (hcomm : A * (C + T) = (C + T) * A) :
    Matrix.trace ((A * C - C * A) * (A * C - C * A)) =
      Matrix.trace ((A * T - T * A) * (A * T - T * A)) := by
  rw [commutator_sq_eq_of_commutes_add A C T hcomm]

/-- Graph-facing form: the antipodal and triangle-free commutator squares
have equal trace for every regular `C₄`-free graph. -/
theorem trace_antipodal_commutator_sq_eq_triangleFree_commutator_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    Matrix.trace ((A * C - C * A) * (A * C - C * A)) =
      Matrix.trace ((A * T - T * A) * (A * T - T * A)) := by
  dsimp only
  apply trace_commutator_sq_eq_of_commutes_add
  rw [← secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G]
  exact adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg

end

end Erdos85
