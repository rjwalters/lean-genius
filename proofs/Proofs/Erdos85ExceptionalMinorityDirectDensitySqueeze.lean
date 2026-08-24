import Proofs.Erdos85DefectPairsComplementBalance
import Proofs.Erdos85DyadicStoppingSupportExcessIncidenceSqueeze
import Proofs.Erdos85ExceptionalMinorityDefectPairPenalty

/-!
# Direct dyadic squeeze with a split exceptional minority

An exceptional defect clique need not lie wholly in the complement of the
marked support.  Splitting it across `B` and `Bᶜ` gives a quadratic lower
bound on the *sum* of their internal defect-pair counts.  Complement balance
gives their difference.  Together these eliminate both pair-count variables
from the optimized service inequality.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Arithmetic elimination of both internal pair counts. -/
theorem splitMinority_pairBudget_complementBalance_eliminate
    {cost budget d b c eB eC r : ℕ}
    (heB : eB ≤ budget)
    (hcost : cost ≤ budget - eB)
    (hbalance : d * b + 2 * eC = 2 * eB + d * c)
    (hminority : r * r ≤ 4 * (eB + eC) + 2 * r) :
    8 * cost + r * r + 2 * (d * b) ≤
      8 * budget + 2 * r + 2 * (d * c) := by
  omega

/-- Graph-facing consumer.  The sole extra hypothesis is the split-minority
quadratic bound; it does not assume the minority lies on either side. -/
theorem c4Free_binarySquare_dyadicStoppingSupport_splitMinority_directDensity_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (j h r : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q)
    (hminority :
      r * r ≤
        4 * ((secondOrderDefectPairs G (dyadicOccupancySupport G S j)).card +
          (secondOrderDefectPairs G
            ((dyadicOccupancySupport G S j)ᶜ : Finset V)).card) + 2 * r) :
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
  dsimp only
  let B := dyadicOccupancySupport G S j
  let eB := (secondOrderDefectPairs G B).card
  let eC := (secondOrderDefectPairs G (Bᶜ : Finset V)).card
  let budget := B.card.choose 2
  let cost :=
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
  have hservice :=
    c4Free_dyadicStoppingSupport_twoShore_convexTangent_cherry_squeeze
      G hfree hreg S j h hdiv hqdiv
  dsimp only at hservice
  rw [hcard] at hservice
  change cost ≤ budget - (zeroCommonNeighborPairs G B).card at hservice
  rw [← secondOrderDefectPairs_eq_zeroCommonNeighborPairs G hfree B] at hservice
  change cost ≤ budget - eB at hservice
  have heB : eB ≤ budget := by
    dsimp only [eB, budget]
    calc
      (secondOrderDefectPairs G B).card ≤ (B.powersetCard 2).card :=
        Finset.card_le_card (secondOrderDefectPairs_subset_powersetCard G B)
      _ = B.card.choose 2 := by simp
  have hbalance :=
    c4Free_binarySquare_secondOrderDefectPairs_complement_balance
      G hfree hq hreg hcard B
  change (q - 1) * B.card + 2 * eC =
      2 * eB + (q - 1) * (q * q - B.card) at hbalance
  change r * r ≤ 4 * (eB + eC) + 2 * r at hminority
  change 8 * cost + r * r + 2 * ((q - 1) * B.card) ≤
    8 * budget + 2 * r + 2 * ((q - 1) * (q * q - B.card))
  exact splitMinority_pairBudget_complementBalance_eliminate
    heB hservice hbalance hminority

/-- Canonical exceptional-profile form of the direct squeeze.  The empty
line family may split arbitrarily across the dyadic support and its
complement; its clique structure and saturated population supply the
quadratic penalty automatically. -/
theorem c4Free_binarySquare_dyadicStoppingSupport_saturatedDeficit_directDensity_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (j h r : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q)
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
  apply c4Free_binarySquare_dyadicStoppingSupport_splitMinority_directDensity_squeeze
    G hfree hq hreg hcard S j h r hdiv hqdiv
  exact saturatedDeficit_splitMinority_quadratic_defectPairPenalty
    G (by omega) hreg S (dyadicOccupancySupport G S j)
      htri hemptyClique hsupportCard hdisplacement

end

end Erdos85

#print axioms Erdos85.splitMinority_pairBudget_complementBalance_eliminate
#print axioms
  Erdos85.c4Free_binarySquare_dyadicStoppingSupport_splitMinority_directDensity_squeeze
#print axioms
  Erdos85.c4Free_binarySquare_dyadicStoppingSupport_saturatedDeficit_directDensity_squeeze
