import Proofs.Erdos85CenteredShoreMoments
import Proofs.Erdos85C4FreeFourthMoment

/-! # Ambient moments of the h305 service graph -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Every 48-vertex, 6-regular, C4-free service graph has the fixed ambient
trace moments required by the residual spectral ledger. -/
theorem serviceGraph_trace_moments_six_regular_fortyEight
    {X : Type*} [Fintype X] [DecidableEq X]
    (C : SimpleGraph X) [DecidableRel C.Adj]
    (hcard : Fintype.card X = 48)
    (hreg : ∀ x, C.degree x = 6)
    (hfree : ¬ containsC4 X C) :
    Matrix.trace ((C.adjMatrix ℂ) ^ 1) = 0 ∧
      Matrix.trace ((C.adjMatrix ℂ) ^ 2) = 288 ∧
      Matrix.trace ((C.adjMatrix ℂ) ^ 4) = 3168 := by
  classical
  have h1 : Matrix.trace ((C.adjMatrix ℂ) ^ 1) = 0 := by
    rw [pow_one]
    exact SimpleGraph.trace_adjMatrix (G := C) (α := ℂ)
  have h2 : Matrix.trace ((C.adjMatrix ℂ) ^ 2) = 288 := by
    rw [pow_two, trace_adjMatrix_sq_complex_eq_sum_degrees]
    simp [hreg, hcard]
    norm_num
  have h4z : Matrix.trace ((C.adjMatrix ℤ) ^ 4) = 3168 := by
    have h := trace_adjMatrix_fourth_of_not_containsC4 C hfree
    have hpow : (C.adjMatrix ℤ) ^ 4 =
        (C.adjMatrix ℤ * C.adjMatrix ℤ) *
          (C.adjMatrix ℤ * C.adjMatrix ℤ) := by noncomm_ring
    rw [← hpow] at h
    simpa [hreg, hcard] using h
  have h4c := trace_complex_adjMatrix_pow_eq_intCast C 4
  rw [h4z] at h4c
  norm_num at h4c
  exact ⟨h1, h2, h4c⟩

end

end Erdos85

#print axioms Erdos85.serviceGraph_trace_moments_six_regular_fortyEight
