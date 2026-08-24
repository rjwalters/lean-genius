import Proofs.Erdos85TwoPoleResidualTransportIdentity
import Proofs.Erdos85EvenExcessOneDefectKernel

/-!
# Exceptional-line correction for a two-pole potential

This evaluates the correction in `(73rnz_bq)` under the exact exceptional
core condition `Dh=h`.  The mod-two defect identity gives `A²h=0`, so the
residual correction is simply `Ah`, the two pole-neighborhood lines.
-/

open SimpleGraph

namespace Erdos85

/-- The all-ones matrix kills a two-coordinate indicator over `F₂`. -/
theorem onesMatrix_mulVec_twoCoordinate_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (pole₁ pole₂ : V) :
    (Matrix.of (fun _ _ => (1 : ZMod 2)) : Matrix V V (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) = 0 := by
  rw [Matrix.mulVec_add, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one]
  funext center
  simp [zmodTwo_add_self]

/-- Under `Dh=h`, the two-pole correction `A²h+Ah` reduces exactly to
`Ah`. -/
theorem twoPoleResidualCorrection_eq_adjMatrix_mulVec_of_defect_fixed
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (antipodalGraph A).Adj]
    (hfree : ¬ containsC4 V A)
    {q : ℕ} (hq : Even q) (hreg : ∀ u, A.degree u = q)
    (pole₁ pole₂ : V)
    (hfixed : ((secondOrderDefectGraph A).adjMatrix (ZMod 2)).mulVec
      (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
        Pi.single pole₁ 1 + Pi.single pole₂ 1) :
    twoPoleResidualCorrection A
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      (A.adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) := by
  let M := A.adjMatrix (ZMod 2)
  let D := (secondOrderDefectGraph A).adjMatrix (ZMod 2)
  let J : Matrix V V (ZMod 2) := Matrix.of fun _ _ => 1
  let h : V → ZMod 2 := Pi.single pole₁ 1 + Pi.single pole₂ 1
  have hsq := adjMatrix_sq_eq_defect_mod_two_of_even_regular
    A hfree hq hreg
  have hJ : J.mulVec h = 0 := by
    exact onesMatrix_mulVec_twoCoordinate_eq_zero pole₁ pole₂
  have hD : D.mulVec h = h := by
    exact hfixed
  have hA2 : (M * M).mulVec h = 0 := by
    change M * M = 1 + J + D at hsq
    rw [hsq, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      hJ, hD]
    funext i
    simp [zmodTwo_add_self]
  change (M * M).mulVec h + M.mulVec h = M.mulVec h
  rw [hA2, zero_add]

/-- Pointwise, `Ah` is the sum of the two pole-neighborhood indicators. -/
theorem adjMatrix_mulVec_twoCoordinate_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (pole₁ pole₂ center : V) :
    (A.adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) center =
      A.adjMatrix (ZMod 2) center pole₁ +
        A.adjMatrix (ZMod 2) center pole₂ := by
  rw [Matrix.mulVec_add, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one]
  rfl

/-- **Exceptional-line transport (`73rnz_bs`).**  When the two-pole vector
is fixed by the defect graph, residual and triangle transport differ exactly
by the two pole-neighborhood lines. -/
theorem binaryTransportResidualGraph_mulVec_eq_triangle_add_poleLines
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (antipodalGraph A).Adj]
    (hfree : ¬ containsC4 V A)
    {q : ℕ} (hq : Even q) (hreg : ∀ u, A.degree u = q)
    (x : V → ZMod 2) (pole₁ pole₂ : V)
    (hAx : (A.adjMatrix (ZMod 2)).mulVec x =
      Pi.single pole₁ 1 + Pi.single pole₂ 1)
    (hfixed : ((secondOrderDefectGraph A).adjMatrix (ZMod 2)).mulVec
      (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
        Pi.single pole₁ 1 + Pi.single pole₂ 1) :
    ((binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2)).mulVec x =
      ((triangleFreeEdgeGraph A).adjMatrix (ZMod 2)).mulVec x +
        (A.adjMatrix (ZMod 2)).mulVec
          (Pi.single pole₁ 1 + Pi.single pole₂ 1) := by
  rw [binaryTransportResidualGraph_mulVec_of_adjMatrix_mulVec_eq
      A hq hreg x _ hAx,
    twoPoleResidualCorrection_eq_adjMatrix_mulVec_of_defect_fixed
      A hfree hq hreg pole₁ pole₂ hfixed]

end Erdos85

#print axioms Erdos85.onesMatrix_mulVec_twoCoordinate_eq_zero
#print axioms Erdos85.twoPoleResidualCorrection_eq_adjMatrix_mulVec_of_defect_fixed
#print axioms Erdos85.adjMatrix_mulVec_twoCoordinate_apply
#print axioms Erdos85.binaryTransportResidualGraph_mulVec_eq_triangle_add_poleLines
