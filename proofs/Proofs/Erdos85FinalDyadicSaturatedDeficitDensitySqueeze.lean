import Proofs.Erdos85FinalDyadicExceptionalProfile
import Proofs.Erdos85ExceptionalMinorityDirectDensitySqueeze

/-!
# Final dyadic saturated-deficit density squeeze

This specializes the split-minority direct-density endpoint to the actual
last dyadic scale.  The scale equation supplies the divisibility of `q`, and
the final occupancy profile supplies the three-level normal form, leaving
only the genuine exceptional-support hypotheses visible.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Final-scale form of the saturated minority direct-density squeeze. -/
theorem c4Free_binarySquare_finalDyadic_saturatedDeficit_directDensity_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 3 ≤ q) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (j h r : ℕ)
    (hqa : q = 2 * 2 ^ j)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hsupportCard : (exceptionalSignedSupport G S q).card = q)
    (hdisplacement :
      2 * (S.card : ℤ) - Fintype.card V = (q : ℤ) - 2 * r) :
    let L := dyadicStoppingServiceMinimum q S.card j
    let M := dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j
    let B := dyadicOccupancySupport G S j
    let E := q * B.card - (S.card * L + (Sᶜ : Finset V).card * M)
    let serviceCost :=
      S.card * L.choose 2 + (Sᶜ : Finset V).card * M.choose 2 +
        min L M * E + (h * E - q * q * (h + 1).choose 2)
    8 * serviceCost + r * r + 2 * ((q - 1) * B.card) ≤
      8 * B.card.choose 2 + 2 * r +
        2 * ((q - 1) * (q * q - B.card)) := by
  have hqdiv : 2 ^ (j + 1) ∣ q := by
    rw [hqa, pow_succ]
    simp [Nat.mul_comm]
  exact c4Free_binarySquare_dyadicStoppingSupport_saturatedDeficit_directDensity_squeeze
    G hfree hq hreg hcard S j h r hdiv hqdiv
      (finalDyadic_occupancy_trichotomy G hqa hreg S hdiv)
      hemptyClique hsupportCard hdisplacement

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_finalDyadic_saturatedDeficit_directDensity_squeeze
