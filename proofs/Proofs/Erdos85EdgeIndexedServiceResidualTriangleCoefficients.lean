import Proofs.Erdos85EdgeIndexedServiceResidualLeadingCoefficients
import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger

/-! # Triangle-count form of the service residual coefficients -/

open Polynomial SimpleGraph

namespace Erdos85

noncomputable section

/-- For a graph adjacency residual with the h305 moment ledger, the third
and fourth non-leading coefficients are explicit affine functions of the
number of adjacency triangles. -/
theorem h305_residual_leading_coefficients_eq_triangleCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV3 : 3 ≤ Fintype.card V)
    (p : ℂ[X]) (hp : p.Monic) (hpdeg : p.natDegree = 32)
    (h1 : complexRootPowerSum p 1 = -8)
    (h2 : complexRootPowerSum p 2 = 224)
    (h3 : complexRootPowerSum p 3 =
      Matrix.trace ((G.adjMatrix ℂ) ^ 3) - 224)
    (h4 : complexRootPowerSum p 4 = 1792) :
    let T := (adjacencyTriangleMinorFinset G).card
    p.coeff 31 = 8 ∧ p.coeff 30 = -80 ∧
      p.coeff 29 = -2 * T - 736 ∧
      p.coeff 28 = 3008 - 16 * T := by
  classical
  dsimp only
  let T := (adjacencyTriangleMinorFinset G).card
  have hint := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount G hV3
  have hpow : (G.adjMatrix ℤ) ^ 3 =
      G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ := by
    simp [pow_succ]
  have htau : Matrix.trace ((G.adjMatrix ℂ) ^ 3) = ((6 * T : ℕ) : ℂ) := by
    rw [trace_complex_adjMatrix_pow_eq_intCast G 3, hpow, hint]
    norm_num [T]
  obtain ⟨hc1, hc2, hc3, hc4⟩ :=
    h305_degreeThirtyTwo_residual_leading_coefficients p hp hpdeg
      h1 h2 (Matrix.trace ((G.adjMatrix ℂ) ^ 3)) h3 h4
  refine ⟨hc1, hc2, ?_, ?_⟩
  · rw [htau] at hc3
    norm_num at hc3 ⊢
    linear_combination (1 / 3) * hc3
  · rw [htau] at hc4
    norm_num at hc4 ⊢
    linear_combination (1 / 3) * hc4

end

end Erdos85

#print axioms Erdos85.h305_residual_leading_coefficients_eq_triangleCount
