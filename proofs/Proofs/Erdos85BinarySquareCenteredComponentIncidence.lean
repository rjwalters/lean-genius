import Proofs.Erdos85BinarySquareComponentIncidenceSelf

/-!
# Centered component-incidence orthogonality

Subtracting the common all-ones direction from each rectangular component
incidence block turns the cross Gram `J` into exact orthogonality and turns
the self Gram into the centered induced defect operator.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Rectangular all-ones matrix. -/
def rectangularOnesMatrix (X Y K : Type*) [One K] : Matrix X Y K :=
  Matrix.of fun _ _ => 1

/-- Integral centering of the ambient-neighbor incidence of one defect
component.  Multiplication by `q` avoids division by the column sum. -/
def centeredDefectComponentNeighborIncidenceMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (c : (secondOrderDefectGraph G).ConnectedComponent) :
    Matrix V c.supp ℤ :=
  (q : ℤ) • defectComponentNeighborIncidenceMatrix (K := ℤ) G c -
    rectangularOnesMatrix V c.supp ℤ

private theorem transpose_incidence_mul_rectangularOnes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    (defectComponentNeighborIncidenceMatrix (K := ℤ) G c).transpose *
        rectangularOnesMatrix V d.supp ℤ =
      (q : ℤ) • rectangularOnesMatrix c.supp d.supp ℤ := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, defectComponentNeighborIncidenceMatrix,
    rectangularOnesMatrix, Matrix.of_apply, mul_one, Matrix.smul_apply,
    smul_eq_mul]
  have hrow : (G.adjMatrix ℤ).mulVec (Function.const V 1) x.1 = (q : ℤ) := by
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg x.1]
  rw [Matrix.mulVec, dotProduct] at hrow
  simpa [SimpleGraph.adjMatrix_apply, G.adj_comm] using hrow

private theorem transpose_rectangularOnes_mul_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    (rectangularOnesMatrix V c.supp ℤ).transpose *
        defectComponentNeighborIncidenceMatrix (K := ℤ) G d =
      (q : ℤ) • rectangularOnesMatrix c.supp d.supp ℤ := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, rectangularOnesMatrix, Matrix.of_apply,
    defectComponentNeighborIncidenceMatrix, one_mul, Matrix.smul_apply,
    smul_eq_mul]
  have hrow : (G.adjMatrix ℤ).mulVec (Function.const V 1) y.1 = (q : ℤ) := by
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg y.1]
  rw [Matrix.mulVec, dotProduct] at hrow
  simpa [SimpleGraph.adjMatrix_apply, G.adj_comm] using hrow

private theorem transpose_rectangularOnes_mul_rectangularOnes
    {V X Y : Type*} [Fintype V] [Fintype X] [Fintype Y] :
    (rectangularOnesMatrix V X ℤ).transpose *
        rectangularOnesMatrix V Y ℤ =
      (Fintype.card V : ℤ) • rectangularOnesMatrix X Y ℤ := by
  ext x y
  simp [Matrix.mul_apply, rectangularOnesMatrix]

/-- **Distinct centered component incidences are exactly orthogonal.** -/
theorem transpose_centeredDefectComponentNeighborIncidenceMatrix_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d) :
    (centeredDefectComponentNeighborIncidenceMatrix G q c).transpose *
        centeredDefectComponentNeighborIncidenceMatrix G q d = 0 := by
  rw [centeredDefectComponentNeighborIncidenceMatrix,
    centeredDefectComponentNeighborIncidenceMatrix,
    Matrix.transpose_sub, Matrix.transpose_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub, smul_smul]
  rw [transpose_defectComponentNeighborIncidenceMatrix_mul_eq_ones
      G hfree c d hcd,
    transpose_incidence_mul_rectangularOnes G hreg c d,
    transpose_rectangularOnes_mul_incidence G hreg c d,
    transpose_rectangularOnes_mul_rectangularOnes, hcard]
  ext x y
  simp [rectangularOnesMatrix, Matrix.zero_apply]

/-- **Centered incidence self Gram.**  Its only surviving block is the
centered induced defect operator. -/
theorem transpose_centeredDefectComponentNeighborIncidenceMatrix_mul_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (centeredDefectComponentNeighborIncidenceMatrix G q c).transpose *
        centeredDefectComponentNeighborIncidenceMatrix G q c =
      ((q * q : ℕ) : ℤ) •
        (((q - 1 : ℕ) : ℤ) • (1 : Matrix c.supp c.supp ℤ) -
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ) := by
  rw [centeredDefectComponentNeighborIncidenceMatrix,
    Matrix.transpose_sub, Matrix.transpose_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub, smul_smul]
  rw [transpose_defectComponentNeighborIncidenceMatrix_mul_self
      G hfree hq hreg c,
    transpose_incidence_mul_rectangularOnes G hreg c c,
    transpose_rectangularOnes_mul_incidence G hreg c c,
    transpose_rectangularOnes_mul_rectangularOnes, hcard]
  push_cast
  simp only [rectangularOnesMatrix]
  module

end

end Erdos85
