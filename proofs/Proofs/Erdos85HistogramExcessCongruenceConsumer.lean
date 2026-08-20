import Proofs.Erdos85CubicTraceModFour
import Proofs.Erdos85ServiceSixthTraceDivisibility
import Proofs.Erdos85HistogramExcessCongruenceThreshold
import Proofs.Erdos85CubicDiagonalHistogram

/-! # Graph-facing sixth-trace congruence thresholds -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The exact h305 histogram excess threshold split by triangle parity. -/
theorem sixRegular_fortyEight_histogramExcess_threshold_by_triangleParity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (hstrict : 61248 < Matrix.trace ((G.adjMatrix ℤ) ^ 6)) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    let E : ℤ := ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
      ∑ b ∈ cubicNonneighborFinset G a,
        (A3 a b - 3) * (A3 a b - 4))
    (Even ((adjacencyTriangleMinorFinset G).card : ℤ) → 204 ≤ E) ∧
      (¬ Even ((adjacencyTriangleMinorFinset G).card : ℤ) → 198 ≤ E) := by
  dsimp only
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let E : ℤ := ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
    ∑ b ∈ cubicNonneighborFinset G a,
      (A3 a b - 3) * (A3 a b - 4))
  have hdiv : (6 : ℤ) ∣ E := by
    simpa [A3, E] using
      six_dvd_sixRegular_fortyEight_histogramExcess G hfree hcard hreg
  have hstrictE : 192 < E := by
    have hs := hstrict
    rw [sixRegular_fortyEight_trace_six_eq_baseline_add_histogramExcess
      G hfree hcard hreg] at hs
    change 61248 < 61056 + E at hs
    omega
  have hmodDvd : (4 : ℤ) ∣
      E - 2 * (adjacencyTriangleMinorFinset G).card := by
    simpa [A3, E] using
      sixRegular_fortyEight_histogramExcess_mod_four G hfree hcard hreg
  have hmod4 : E % 4 =
      (2 * ((adjacencyTriangleMinorFinset G).card : ℤ)) % 4 := by
    rcases hmodDvd with ⟨k, hk⟩
    omega
  exact histogramExcess_threshold_of_mod_four_triangle E
    ((adjacencyTriangleMinorFinset G).card : ℤ)
    hdiv hstrictE hmod4

/-- Concrete diagonal-bin consumer: even total population in the `q=2`
and `q=6` bins forces the stronger excess threshold `204`. -/
theorem sixRegular_fortyEight_histogramExcess_ge_204_of_even_diagBins
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (hstrict : 61248 < Matrix.trace ((G.adjMatrix ℤ) ^ 6))
    (hdiag : Even (cubicDiagonalHistogram G 2 +
      cubicDiagonalHistogram G 6)) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    204 ≤ ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
      ∑ b ∈ cubicNonneighborFinset G a,
        (A3 a b - 3) * (A3 a b - 4)) := by
  dsimp only
  apply (sixRegular_fortyEight_histogramExcess_threshold_by_triangleParity
    G hfree hcard hreg hstrict).1
  have hpar :=
    sixRegular_fortyEight_triangleCount_mod_two_eq_diagTwo_add_diagSix
      G hfree hcard hreg
  rcases hdiag with ⟨r, hr⟩
  refine ⟨((adjacencyTriangleMinorFinset G).card : ℤ) / 2, ?_⟩
  have hright : (cubicDiagonalHistogram G 2 +
      cubicDiagonalHistogram G 6) % 2 = 0 := by omega
  rw [hright] at hpar
  omega

end

end Erdos85

#print axioms
  Erdos85.sixRegular_fortyEight_histogramExcess_threshold_by_triangleParity
#print axioms
  Erdos85.sixRegular_fortyEight_histogramExcess_ge_204_of_even_diagBins
