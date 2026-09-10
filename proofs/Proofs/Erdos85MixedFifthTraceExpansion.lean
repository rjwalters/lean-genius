import Mathlib

/-! Nonregular fifth-trace algebra. The degree-correction matrix K is not
assumed scalar. The numerical specialization lists the trace evaluations
that must be supplied by the order49 graph ledger. -/
namespace Erdos85
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Expand the mixed defect trace without imposing regularity. -/
theorem mixed_defect_fifth_trace_expansion
    (A K J D : Matrix V V ℤ)
    (hA : Aᵀ = A) (hK : Kᵀ = K) (hJ : Jᵀ = J)
    (hD : D = K+J-A^2) :
    Matrix.trace (A*D^2) = Matrix.trace (A^5) -
      2*Matrix.trace (A^3*K) - 2*Matrix.trace (A^3*J) +
      Matrix.trace (A*K^2) + Matrix.trace (A*J^2) +
      2*Matrix.trace (A*K*J) := by
  have hcycle (B : Matrix V V ℤ) :
      Matrix.trace (A*B*A^2) = Matrix.trace (A^3*B) := by
    rw [Matrix.trace_mul_cycle]
    congr 1
  have hcross : Matrix.trace (A*J*K) = Matrix.trace (A*K*J) := by
    calc
      Matrix.trace (A*J*K) = Matrix.trace ((A*J*K)ᵀ) := (Matrix.trace_transpose _).symm
      _ = Matrix.trace (K*J*A) := by
        simp only [Matrix.transpose_mul, hA, hK, hJ, Matrix.mul_assoc]
      _ = Matrix.trace (A*K*J) := Matrix.trace_mul_cycle K J A
  have hexp : A*D^2 = A*K^2 + A*K*J - A*K*A^2 + A*J*K + A*J^2 -
      A*J*A^2 - A^3*K - A^3*J + A^5 := by
    rw [hD]
    noncomm_ring
  rw [hexp]
  simp only [Matrix.trace_add, Matrix.trace_sub, hcycle, hcross]
  ring

/-- Numerical q7 specialization, conditional on the listed graph trace ledger. -/
theorem q7_fifth_trace_of_mixed_trace_ledger
    (A K J D : Matrix V V ℤ)
    (hA : Aᵀ = A) (hK : Kᵀ = K) (hJ : Jᵀ = J)
    (hD : D = K+J-A^2) (h T : ℤ)
    (hA3K : Matrix.trace (A^3*K) = 36*T+152*h)
    (hA3J : Matrix.trace (A^3*J) = 16807+161*h)
    (hAK2 : Matrix.trace (A*K^2) = 0)
    (hAJ2 : Matrix.trace (A*J^2) = 16807+49*h)
    (hAKJ : Matrix.trace (A*K*J) = 2058+14*h) :
    Matrix.trace (A^5) = 12691+549*h+72*T+Matrix.trace (A*D^2) := by
  have hm := mixed_defect_fifth_trace_expansion A K J D hA hK hJ hD
  rw [hA3K,hA3J,hAK2,hAJ2,hAKJ] at hm
  linarith
end Erdos85
