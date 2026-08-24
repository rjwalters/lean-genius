import Proofs.Erdos85DefectPairsComplementBalance
import Proofs.Erdos85DyadicStoppingSupportExcessIncidenceSqueeze
import Proofs.Erdos85FullEmptyCrossDefectPenalty

/-!
# Direct final-dyadic density squeeze with the full-empty penalty

At the final dyadic scale, the complement of the stopping support is the
canonical full/empty exceptional family.  Its complete bipartite defect
subgraph contributes `|F| |E|` internal defect pairs.  Exact complement
balance transfers that penalty into the optimized service inequality while
eliminating the unknown defect-pair count on the stopping support.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Final-scale graph-facing squeeze retaining the unconditional cross
penalty between full and empty line centers. -/
theorem c4Free_binarySquare_finalDyadicSupport_fullEmpty_directDensity_squeeze
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
    2 * serviceCost + (q - 1) * B.card +
        2 * ((fullLineCenters G S q).card *
          (emptyLineCenters G S).card) ≤
      2 * B.card.choose 2 +
        (q - 1) * (q * q - B.card) := by
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
  have hqdiv : 2 ^ (j + 1) ∣ q := by
    rw [hqa, pow_succ]
    simp [Nat.mul_comm]
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
  have helim := pairBudget_complementBalance_eliminate
    heB hservice hbalance
  have hcross :=
    full_mul_empty_le_compl_finalDyadicSupport_secondOrderDefectPairs
      G hfree (by omega) hqa hreg S hdiv
  change (fullLineCenters G S q).card *
      (emptyLineCenters G S).card ≤ eC at hcross
  change 2 * cost + (q - 1) * B.card +
      2 * ((fullLineCenters G S q).card *
        (emptyLineCenters G S).card) ≤
    2 * budget + (q - 1) * (q * q - B.card)
  omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_finalDyadicSupport_fullEmpty_directDensity_squeeze
