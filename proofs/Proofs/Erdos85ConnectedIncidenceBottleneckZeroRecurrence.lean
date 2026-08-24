import Proofs.Erdos85ConnectedIncidenceBottleneckBlindSpot

/-!
# A zero bottleneck row forces the defect clique recurrence

Let `E = AD-(J-A)`.  Multiplying on the left by `A` and using the defect
square identity gives

`AE = -D² + (q-2)D + (q-1)I`.

Thus a zero column of `E` forces the corresponding defect-neighborhood
indicator to satisfy the saturated-clique recurrence

`D²e_x = (q-2)De_x + (q-1)e_x`.

The graph-facing consumer reads this entrywise and contradicts an edge
escaping the closed defect neighborhood.
-/

namespace Erdos85

noncomputable section

/-- Exact left-multiple identity behind the saturated-clique recurrence. -/
theorem incidenceBottleneck_left_mul_eq_defect_recurrence
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D J E : Matrix V V ℚ) (q : ℕ)
    (hE : E = A * D - (J - A))
    (hsq : A * A = ((q : ℚ) - 1) • (1 : Matrix V V ℚ) + J - D)
    (hAJ : A * J = (q : ℚ) • J)
    (hJD : J * D = ((q : ℚ) - 1) • J) :
    A * E = -(D * D) + ((q : ℚ) - 2) • D +
      ((q : ℚ) - 1) • (1 : Matrix V V ℚ) := by
  rw [hE, Matrix.mul_sub, Matrix.mul_sub, hAJ]
  rw [← Matrix.mul_assoc, hsq]
  rw [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hJD]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- A vanishing bottleneck column forces the exact defect-square recurrence
on that column. -/
theorem defect_recurrence_of_incidenceBottleneck_mulVec_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D J E : Matrix V V ℚ) (q : ℕ) (v : V → ℚ)
    (hleft : A * E = -(D * D) + ((q : ℚ) - 2) • D +
      ((q : ℚ) - 1) • (1 : Matrix V V ℚ))
    (hzero : E.mulVec v = 0) :
    (D * D).mulVec v =
      ((q : ℚ) - 2) • D.mulVec v + ((q : ℚ) - 1) • v := by
  have hz : (A * E).mulVec v = 0 := by
    calc
      (A * E).mulVec v = A.mulVec (E.mulVec v) :=
        (Matrix.mulVec_mulVec v A E).symm
      _ = A.mulVec 0 := by rw [hzero]
      _ = 0 := Matrix.mulVec_zero A
  rw [hleft, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.neg_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hz
  ext i
  have hi := congrFun hz i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply,
    smul_eq_mul] at hi ⊢
  linarith

/-- Composed form from the defining bottleneck and square identities. -/
theorem defect_recurrence_of_incidenceBottleneck_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D J E : Matrix V V ℚ) (q : ℕ) (v : V → ℚ)
    (hE : E = A * D - (J - A))
    (hsq : A * A = ((q : ℚ) - 1) • (1 : Matrix V V ℚ) + J - D)
    (hAJ : A * J = (q : ℚ) • J)
    (hJD : J * D = ((q : ℚ) - 1) • J)
    (hzero : E.mulVec v = 0) :
    (D * D).mulVec v =
      ((q : ℚ) - 2) • D.mulVec v + ((q : ℚ) - 1) • v := by
  apply defect_recurrence_of_incidenceBottleneck_mulVec_eq_zero
    A D J E q v
  · exact incidenceBottleneck_left_mul_eq_defect_recurrence
      A D J E q hE hsq hAJ hJD
  · exact hzero

end

end Erdos85

#print axioms Erdos85.incidenceBottleneck_left_mul_eq_defect_recurrence
#print axioms Erdos85.defect_recurrence_of_incidenceBottleneck_mulVec_eq_zero
#print axioms Erdos85.defect_recurrence_of_incidenceBottleneck_zero
