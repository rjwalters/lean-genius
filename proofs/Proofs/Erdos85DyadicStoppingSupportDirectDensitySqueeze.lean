import Proofs.Erdos85DefectPairsSupportDensity
import Proofs.Erdos85DyadicStoppingSupportExcessIncidenceSqueeze

/-!
# Direct density-corrected dyadic stopping squeeze

The excess-incidence squeeze leaves the number of zero-common-neighbor pairs
as an auxiliary variable.  Defect regularity gives a lower bound for that
variable from the marked-support size.  Eliminating it produces a direct
inequality in the four arithmetic parameters `q`, `|S|`, `j`, and `|B|`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- **Direct density-corrected stopping squeeze.**  The complete nonuniform
service cost, doubled, plus the defect-density charge on `B`, fits into the
doubled pair budget plus the capacity of the complement of `B`. -/
theorem c4Free_binarySquare_dyadicStoppingSupport_directDensity_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    let L := dyadicStoppingServiceMinimum q S.card j
    let M := dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j
    let B := dyadicOccupancySupport G S j
    let serviceCost :=
      S.card * L.choose 2 + (Sᶜ : Finset V).card * M.choose 2 +
        min L M *
          (q * B.card - (S.card * L + (Sᶜ : Finset V).card * M))
    2 * serviceCost + (q - 1) * B.card ≤
      2 * B.card.choose 2 + (q - 1) * (q * q - B.card) := by
  dsimp only
  let B := dyadicOccupancySupport G S j
  let Z := zeroCommonNeighborPairs G B
  have hservice :=
    c4Free_dyadicStoppingSupport_twoShore_excessIncidence_cherry_squeeze
      G hfree hreg S j hdiv hqdiv
  have hdensity := binarySquare_secondOrderDefectPairs_support_density
    G hcard (binarySquare_regular_secondOrderDefect_degree_eq
      G hfree hq hreg hcard) B
  have hpairEq := secondOrderDefectPairs_eq_zeroCommonNeighborPairs G hfree B
  change secondOrderDefectPairs G B = Z at hpairEq
  have hZle : Z.card ≤ B.card.choose 2 := by
    rw [← hpairEq]
    calc
      (secondOrderDefectPairs G B).card ≤ (B.powersetCard 2).card :=
        Finset.card_le_card (secondOrderDefectPairs_subset_powersetCard G B)
      _ = B.card.choose 2 := by simp
  rw [hpairEq] at hdensity
  change
    S.card * (dyadicStoppingServiceMinimum q S.card j).choose 2 +
          (Sᶜ : Finset V).card *
            (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j).choose 2 +
          min (dyadicStoppingServiceMinimum q S.card j)
              (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j) *
            (q * B.card -
              (S.card * dyadicStoppingServiceMinimum q S.card j +
                (Sᶜ : Finset V).card *
                  dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j)) ≤
        B.card.choose 2 - Z.card at hservice
  change
    2 * (S.card * (dyadicStoppingServiceMinimum q S.card j).choose 2 +
          (Sᶜ : Finset V).card *
            (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j).choose 2 +
          min (dyadicStoppingServiceMinimum q S.card j)
              (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j) *
            (q * B.card -
              (S.card * dyadicStoppingServiceMinimum q S.card j +
                (Sᶜ : Finset V).card *
                  dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j))) +
        (q - 1) * B.card ≤
      2 * B.card.choose 2 + (q - 1) * (q * q - B.card)
  omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_dyadicStoppingSupport_directDensity_squeeze
