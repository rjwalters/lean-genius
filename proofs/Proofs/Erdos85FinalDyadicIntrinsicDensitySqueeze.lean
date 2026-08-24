import Proofs.Erdos85FullEmptyDirectDensitySqueeze
import Proofs.Erdos85FinalDyadicExceptionalPopulationProduct

/-!
# Intrinsic final dyadic density squeeze

The full×empty direct-density penalty can be written without either
population variable.  After doubling, its contribution is exactly support
size squared minus shore displacement squared.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Population-free integer form of the final-scale direct-density squeeze. -/
theorem c4Free_binarySquare_finalDyadicSupport_intrinsic_directDensity_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hq : 3 ≤ q) (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (h : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    let L := dyadicStoppingServiceMinimum q S.card j
    let M := dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j
    let B := dyadicOccupancySupport G S j
    let E := q * B.card - (S.card * L + (Sᶜ : Finset V).card * M)
    let serviceCost :=
      S.card * L.choose 2 + (Sᶜ : Finset V).card * M.choose 2 +
        min L M * E + (h * E - q * q * (h + 1).choose 2)
    4 * (serviceCost : ℤ) +
        2 * (((q - 1) * B.card : ℕ) : ℤ) +
        ((exceptionalSignedSupport G S q).card : ℤ) ^ 2 -
        (2 * (S.card : ℤ) - Fintype.card V) ^ 2 ≤
      4 * (B.card.choose 2 : ℤ) +
        2 * (((q - 1) * (q * q - B.card) : ℕ) : ℤ) := by
  dsimp only
  let B := dyadicOccupancySupport G S j
  let serviceCost :=
    S.card * (dyadicStoppingServiceMinimum q S.card j).choose 2 +
      (Sᶜ : Finset V).card *
        (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j).choose 2 +
      min (dyadicStoppingServiceMinimum q S.card j)
          (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j) *
        (q * B.card -
          (S.card * dyadicStoppingServiceMinimum q S.card j +
            (Sᶜ : Finset V).card *
              dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j)) +
      (h * (q * B.card -
          (S.card * dyadicStoppingServiceMinimum q S.card j +
            (Sᶜ : Finset V).card *
              dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j)) -
        q * q * (h + 1).choose 2)
  have hbase :=
    c4Free_binarySquare_finalDyadicSupport_fullEmpty_directDensity_squeeze
      G hfree hq hqa hreg hcard S h hdiv
  change 2 * serviceCost + (q - 1) * B.card +
      2 * ((fullLineCenters G S q).card *
        (emptyLineCenters G S).card) ≤
    2 * B.card.choose 2 + (q - 1) * (q * q - B.card) at hbase
  have hbaseZ :
      2 * (serviceCost : ℤ) + (((q - 1) * B.card : ℕ) : ℤ) +
          2 * (((fullLineCenters G S q).card *
            (emptyLineCenters G S).card : ℕ) : ℤ) ≤
        2 * (B.card.choose 2 : ℤ) +
          (((q - 1) * (q * q - B.card) : ℕ) : ℤ) := by
    exact_mod_cast hbase
  have hproduct := finalDyadic_exceptional_population_product_identity
    G hqa hreg S hdiv
  change
    4 * (serviceCost : ℤ) +
        2 * (((q - 1) * B.card : ℕ) : ℤ) +
        ((exceptionalSignedSupport G S q).card : ℤ) ^ 2 -
        (2 * (S.card : ℤ) - Fintype.card V) ^ 2 ≤
      4 * (B.card.choose 2 : ℤ) +
        2 * (((q - 1) * (q * q - B.card) : ℕ) : ℤ)
  nlinarith

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_finalDyadicSupport_intrinsic_directDensity_squeeze
