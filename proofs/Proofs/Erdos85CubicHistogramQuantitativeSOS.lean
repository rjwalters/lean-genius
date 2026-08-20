import Proofs.Erdos85CubicTraceHistogramExcess
import Proofs.Erdos85ResidualSixthMomentCubicCertificate

/-! # Quantitative spectral constraint on the cubic histogram -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The residual cubic SOS certificate, expressed entirely in the finite
graph histogram coordinates.  The right side is the global excess above the
spectral equality baseline `192`, while the left side measures the triangle
count's distance from the impossible value `160/6`. -/
theorem sixRegular_fortyEight_histogramExcess_quantitative_triangle
    {V Y : Type*} [Fintype V] [DecidableEq V]
    [Fintype Y] [DecidableEq Y]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Matrix Y Y ℂ) (p : Polynomial ℂ)
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (hB : B.IsHermitian)
    (hp : p ≠ 0) (hdegree : p.natDegree = 32)
    (hfactor : (G.adjMatrix ℂ).charpoly = p * B.charpoly)
    (h1 : complexRootPowerSum p 1 = -8)
    (h2 : complexRootPowerSum p 2 = 224)
    (h3 : complexRootPowerSum p 3 =
      ((6 * (adjacencyTriangleMinorFinset G).card - 224 : ℤ) : ℂ))
    (h4 : complexRootPowerSum p 4 = 1792)
    (hB6 : Matrix.trace (B ^ 6) = 46912) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    let E : ℤ := ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
      ∑ b ∈ cubicNonneighborFinset G a,
        (A3 a b - 3) * (A3 a b - 4))
    (24864 : ℝ) *
        (((6 * (adjacencyTriangleMinorFinset G).card - 160 : ℤ) : ℝ) ^ 2) ≤
      788544 * (((E - 192 : ℤ) : ℝ)) := by
  dsimp only
  have hcert := hermitianResidual_sixthMoment_triangle_certificate
    (G.adjMatrix ℂ) B p ((adjacencyTriangleMinorFinset G).card : ℤ)
    (SimpleGraph.isHermitian_adjMatrix ℂ G) hB hp hdegree hfactor
    h1 h2 h3 h4 hB6
  have hcast := trace_complex_adjMatrix_pow_eq_intCast G 6
  rw [hcast] at hcert
  have hledger :=
    sixRegular_fortyEight_trace_six_eq_baseline_add_histogramExcess
      G hfree hcard hreg
  rw [hledger] at hcert
  have hreCast (z : ℤ) : ((z : ℂ).re : ℝ) = (z : ℝ) := by
    norm_num
  rw [hreCast] at hcert
  norm_num [map_pow] at hcert ⊢
  nlinarith [hcert]

end

end Erdos85

#print axioms
  Erdos85.sixRegular_fortyEight_histogramExcess_quantitative_triangle
