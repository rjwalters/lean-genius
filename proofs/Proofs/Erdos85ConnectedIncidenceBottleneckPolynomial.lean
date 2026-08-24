import Proofs.Erdos85BinarySquareConnectedTraceEscape

/-!
# Polynomial form of the connected incidence bottleneck

At square order let `A` be the ambient adjacency matrix, `D` the
second-order defect adjacency matrix, and `J` the all-ones matrix.  The
integral incidence error used in the connected-defect route is

`E = A D - (J - A)`.

The defect square identity eliminates `D` and expresses this error as the
single odd polynomial in `A`, up to the principal rank-one term:

`E = q A - A^3 + (q-1) J`.

On the nonprincipal space this has multiplier `theta * (q-theta^2)`, or
equivalently `theta * (mu+1)` when `mu = q-1-theta^2` is the defect
eigenvalue.  This file records the exact matrix identity needed before the
row-energy and designated-factor arguments are combined.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Abstract algebraic form of the incidence-bottleneck polynomial identity. -/
theorem incidenceBottleneck_eq_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D J : Matrix V V ℚ) (q : ℕ)
    (hsq : A * A = ((q : ℚ) - 1) • (1 : Matrix V V ℚ) + J - D)
    (hAJ : A * J = (q : ℚ) • J) :
    A * D - (J - A) =
      (q : ℚ) • A - A * A * A + ((q : ℚ) - 1) • J := by
  have hD : D = ((q : ℚ) - 1) • (1 : Matrix V V ℚ) + J - A * A := by
    rw [hsq]
    noncomm_ring
  rw [hD, Matrix.mul_sub, Matrix.mul_add, hAJ]
  simp only [Matrix.mul_smul, Matrix.mul_one]
  rw [Matrix.mul_assoc]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Graph-facing polynomial identity for the square-order second-order
defect incidence bottleneck.  The cardinality hypothesis is intentionally
absent: the identity only needs regularity and the C4-free defect equation. -/
theorem binarySquare_regular_incidenceBottleneck_eq_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q) :
    let A := G.adjMatrix ℚ
    let D := (secondOrderDefectGraph G).adjMatrix ℚ
    let J := ratOnesMatrix V
    A * D - (J - A) =
      (q : ℚ) • A - A * A * A + ((q : ℚ) - 1) • J := by
  dsimp only
  apply incidenceBottleneck_eq_cubic
  · exact adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat G hfree hreg
  · exact adjMatrix_comm_ratOnesMatrix_of_regular G hreg |>.trans
      (ratOnesMatrix_mul_adjMatrix_of_regular G hreg)

end

end Erdos85

#print axioms Erdos85.incidenceBottleneck_eq_cubic
#print axioms Erdos85.binarySquare_regular_incidenceBottleneck_eq_cubic
