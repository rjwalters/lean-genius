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

/-- Expansion of a commutator-square trace into the difference of the two
fourth words.  Cyclicity of trace identifies the three repeated words. -/
theorem trace_commutator_sq_eq_two_mul_alternating_sub_square
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A X : Matrix ι ι ℤ) :
    Matrix.trace ((A * X - X * A) * (A * X - X * A)) =
      2 * (Matrix.trace ((A * X) * (A * X)) -
        Matrix.trace ((A * A) * (X * X))) := by
  have hcross : Matrix.trace ((A * X) * (X * A)) =
      Matrix.trace ((A * A) * (X * X)) := by
    calc
      Matrix.trace ((A * X) * (X * A)) =
          Matrix.trace (((A * X) * X) * A) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (A * ((A * X) * X)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((A * A) * (X * X)) := by
        congr 1
        noncomm_ring
  have hcross' : Matrix.trace ((X * A) * (A * X)) =
      Matrix.trace ((A * A) * (X * X)) := by
    rw [Matrix.trace_mul_comm]
    exact hcross
  have halt : Matrix.trace ((X * A) * (X * A)) =
      Matrix.trace ((A * X) * (A * X)) := by
    calc
      Matrix.trace ((X * A) * (X * A)) =
          Matrix.trace (((X * A) * X) * A) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (A * ((X * A) * X)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((A * X) * (A * X)) := by
        congr 1
        noncomm_ring
  rw [sub_mul, mul_sub, mul_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_sub, hcross, hcross', halt]
  ring

/-- **Expanded color-commutator equation.** -/
theorem trace_square_sub_alternating_eq_of_commutes_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C T : Matrix ι ι ℤ)
    (hcomm : A * (C + T) = (C + T) * A) :
    Matrix.trace ((A * A) * (C * C)) -
        Matrix.trace ((A * C) * (A * C)) =
      Matrix.trace ((A * A) * (T * T)) -
        Matrix.trace ((A * T) * (A * T)) := by
  have hsq := trace_commutator_sq_eq_of_commutes_add A C T hcomm
  rw [trace_commutator_sq_eq_two_mul_alternating_sub_square A C,
    trace_commutator_sq_eq_two_mul_alternating_sub_square A T] at hsq
  omega

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

/-- **Independent mixed fourth-moment equation.**  The triangle-free
alternating word has been eliminated using the `C₄`-free subgraph identity;
the antipodal alternating word remains as the new color parameter. -/
theorem trace_adj_sq_antipodal_sq_sub_alternating_eq_triangleFree_gap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    Matrix.trace ((A * A) * (C * C)) -
        Matrix.trace ((A * C) * (A * C)) =
      Matrix.trace ((A * A) * (T * T)) -
        Matrix.trace ((T * T) * (T * T)) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  have hcomm : A * (C + T) = (C + T) * A := by
    dsimp [A, C, T]
    rw [← secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G]
    exact adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hmain := trace_square_sub_alternating_eq_of_commutes_add A C T hcomm
  have hTG : triangleFreeEdgeGraph G ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have halt := trace_adj_subgraph_adj_subgraph_eq_trace_subgraph_fourth
    G (triangleFreeEdgeGraph G) hfree hTG
  change Matrix.trace ((A * T) * (A * T)) =
    Matrix.trace ((T * T) * (T * T)) at halt
  rw [halt] at hmain
  exact hmain

end

end Erdos85
