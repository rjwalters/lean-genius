import Proofs.Erdos85ResidualCharpolyPowerSums
import Proofs.Erdos85OrderSixtyFourDefectSecondMoment

/-! # Trace moments of the centered h305 shore operator -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem adjMatrix_mul_edgeIndexedVertexOnesMatrix_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (hreg : ∀ x, H.degree x = d) :
    H.adjMatrix ℂ * edgeIndexedVertexOnesMatrix V =
      (d : ℂ) • edgeIndexedVertexOnesMatrix V := by
  classical
  ext x z
  simp only [Matrix.mul_apply, Matrix.smul_apply,
    edgeIndexedVertexOnesMatrix, mul_one, smul_eq_mul]
  trans (((Finset.univ.filter fun y ↦ H.Adj x y).card : ℕ) : ℂ)
  · rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro y _
    simp [SimpleGraph.adjMatrix_apply]
  · have hfilt : Finset.univ.filter (fun y ↦ H.Adj x y) =
        H.neighborFinset x := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilt, ← SimpleGraph.degree, hreg]

theorem edgeIndexedVertexOnesMatrix_mul_adjMatrix_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (hreg : ∀ x, H.degree x = d) :
    edgeIndexedVertexOnesMatrix V * H.adjMatrix ℂ =
      (d : ℂ) • edgeIndexedVertexOnesMatrix V := by
  classical
  ext z x
  simp only [Matrix.mul_apply, Matrix.smul_apply,
    edgeIndexedVertexOnesMatrix, one_mul, smul_eq_mul]
  trans (((Finset.univ.filter fun y ↦ H.Adj x y).card : ℕ) : ℂ)
  · rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro y _
    simp [SimpleGraph.adjMatrix_apply, H.adj_comm]
  · have hfilt : Finset.univ.filter (fun y ↦ H.Adj x y) =
        H.neighborFinset x := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilt, ← SimpleGraph.degree, hreg]
    norm_num

theorem edgeIndexedVertexOnesMatrix_sq
    {V : Type*} [Fintype V] [DecidableEq V] :
    edgeIndexedVertexOnesMatrix V * edgeIndexedVertexOnesMatrix V =
      (Fintype.card V : ℂ) • edgeIndexedVertexOnesMatrix V := by
  classical
  ext x y
  simp [Matrix.mul_apply, edgeIndexedVertexOnesMatrix]

theorem trace_edgeIndexedVertexOnesMatrix
    {V : Type*} [Fintype V] [DecidableEq V] :
    Matrix.trace (edgeIndexedVertexOnesMatrix V) = (Fintype.card V : ℂ) := by
  classical
  simp [Matrix.trace, Matrix.diag, edgeIndexedVertexOnesMatrix]

/-- For a 2-regular graph on 16 vertices with the h305 third and fourth
adjacency moments, the centered operator `(1/2)J-A` has the fixed quotient
moments `8,64,224,1376`. -/
theorem centeredShore_trace_moments
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x, H.degree x = 2)
    (hthree : Matrix.trace ((H.adjMatrix ℂ) ^ 3) = 0)
    (hfour : Matrix.trace ((H.adjMatrix ℂ) ^ 4) = 96) :
    let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
    Matrix.trace (B ^ 1) = 8 ∧
      Matrix.trace (B ^ 2) = 64 ∧
      Matrix.trace (B ^ 3) = 224 ∧
      Matrix.trace (B ^ 4) = 1376 := by
  classical
  dsimp only
  let J := edgeIndexedVertexOnesMatrix V
  let A := H.adjMatrix ℂ
  let B := (2 : ℂ)⁻¹ • J - A
  have hAJ : A * J = (2 : ℂ) • J :=
    adjMatrix_mul_edgeIndexedVertexOnesMatrix_of_regular H 2 hreg
  have hJA : J * A = (2 : ℂ) • J :=
    edgeIndexedVertexOnesMatrix_mul_adjMatrix_of_regular H 2 hreg
  have hJJ : J * J = (16 : ℂ) • J := by
    simpa [hcard] using (edgeIndexedVertexOnesMatrix_sq (V := V))
  have htrJ : Matrix.trace J = 16 := by
    simpa [J, hcard] using (trace_edgeIndexedVertexOnesMatrix (V := V))
  have htrA : Matrix.trace A = 0 := by
    exact SimpleGraph.trace_adjMatrix (G := H) (α := ℂ)
  have htrA2 : Matrix.trace (A ^ 2) = 32 := by
    rw [pow_two, trace_adjMatrix_sq_complex_eq_sum_degrees]
    simp [hreg, hcard]
    norm_num
  have hB1 : B ^ 1 = (2 : ℂ)⁻¹ • J - A := by simp [B]
  have hB2 : B ^ 2 = (2 : ℂ) • J + A ^ 2 := by
    calc
      B ^ 2 = ((2 : ℂ)⁻¹ • J - A) * ((2 : ℂ)⁻¹ • J - A) := by
        simp [B, pow_two]
      _ = (4 : ℂ)⁻¹ • (J * J) - (2 : ℂ)⁻¹ • (J * A) -
          (2 : ℂ)⁻¹ • (A * J) + A ^ 2 := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
          Matrix.mul_smul, pow_two]
        norm_num
        module
      _ = (2 : ℂ) • J + A ^ 2 := by
        rw [hJJ, hJA, hAJ]
        module
  have hJA2 : J * A ^ 2 = (4 : ℂ) • J := by
    rw [pow_two, ← Matrix.mul_assoc, hJA, Matrix.smul_mul, hJA]
    module
  have hA2J : A ^ 2 * J = (4 : ℂ) • J := by
    rw [pow_two, Matrix.mul_assoc, hAJ, Matrix.mul_smul, hAJ]
    module
  have hB3 : B ^ 3 = (14 : ℂ) • J - A ^ 3 := by
    calc
      B ^ 3 = B ^ 2 * B := by noncomm_ring
      _ = ((2 : ℂ) • J + A ^ 2) * ((2 : ℂ)⁻¹ • J - A) := by
        rw [hB2]
      _ = (1 : ℂ) • (J * J) - (2 : ℂ) • (J * A) +
          (2 : ℂ)⁻¹ • (A ^ 2 * J) - A ^ 3 := by
        simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul,
          Matrix.mul_smul, pow_succ, pow_zero]
        norm_num
        module
      _ = (14 : ℂ) • J - A ^ 3 := by
        rw [hJJ, hJA, hA2J]
        module
  have hB4 : B ^ 4 = (80 : ℂ) • J + A ^ 4 := by
    calc
      B ^ 4 = B ^ 2 * B ^ 2 := by noncomm_ring
      _ = ((2 : ℂ) • J + A ^ 2) * ((2 : ℂ) • J + A ^ 2) := by
        rw [hB2]
      _ = (4 : ℂ) • (J * J) + (2 : ℂ) • (J * A ^ 2) +
          (2 : ℂ) • (A ^ 2 * J) + A ^ 4 := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
          Matrix.mul_smul]
        rw [← pow_add]
        norm_num
        module
      _ = (80 : ℂ) • J + A ^ 4 := by
        rw [hJJ, hJA2, hA2J]
        module
  change Matrix.trace (B ^ 1) = 8 ∧
    Matrix.trace (B ^ 2) = 64 ∧ Matrix.trace (B ^ 3) = 224 ∧
      Matrix.trace (B ^ 4) = 1376
  constructor
  · rw [hB1, Matrix.trace_sub, Matrix.trace_smul, htrJ, htrA]
    norm_num
  constructor
  · rw [hB2, Matrix.trace_add, Matrix.trace_smul, htrJ, htrA2]
    norm_num
  constructor
  · rw [hB3, Matrix.trace_sub, Matrix.trace_smul, htrJ]
    rw [show Matrix.trace (A ^ 3) = 0 by simpa [A] using hthree]
    norm_num
  · rw [hB4, Matrix.trace_add, Matrix.trace_smul, htrJ]
    rw [show Matrix.trace (A ^ 4) = 96 by simpa [A] using hfour]
    norm_num

end

end Erdos85

#print axioms Erdos85.centeredShore_trace_moments
