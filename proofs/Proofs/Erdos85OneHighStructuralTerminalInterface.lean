import Proofs.Erdos85OrderFortyNineOneHighStructuralCapstone
import Proofs.Erdos85OrderFortyNineStrataCapstone

/-! # Independent terminal obligations for the one-high structural split -/

namespace Erdos85

open SimpleGraph

noncomputable section

def OneHighAllEvenSectorExcluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (hfree : ¬ containsC4 (Fin 49) G) →
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
    (hHigh : (orderFortyNineHighVertices G).card = 1) →
    ∀ {v : Fin 49} (hv : G.degree v = 8)
      (p : OneHighRawV2Presentation G hfree v),
      let m := exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x))
      (∀ key ∈ exchangedMissPairKeys (Fin 8), Even (m key)) → False

def OneHighMateMissHexagonSectorExcluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (hfree : ¬ containsC4 (Fin 49) G) →
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
    (hHigh : (orderFortyNineHighVertices G).card = 1) →
    ∀ {v : Fin 49} (hv : G.degree v = 8)
      (_p : OneHighRawV2Presentation G hfree v),
      Nonempty (OneHighMateMissHexagon G v) → False

def OneHighThreePairTurnSectorExcluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (hfree : ¬ containsC4 (Fin 49) G) →
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
    (hHigh : (orderFortyNineHighVertices G).card = 1) →
    ∀ {v : Fin 49} (hv : G.degree v = 8)
      (p : OneHighRawV2Presentation G hfree v),
      let m := exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x))
      OneHighOddSupportThreePairTurnProp m → False

def OneHighCrossBlockSectorExcluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (hfree : ¬ containsC4 (Fin 49) G) →
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
    (hHigh : (orderFortyNineHighVertices G).card = 1) →
    ∀ {v : Fin 49} (hv : G.degree v = 8)
      (p : OneHighRawV2Presentation G hfree v),
      let m := exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x))
      OneHighOddSupportCrossBlockProp m → False

/-- Closing the four independent structural terminals closes the complete
one-high stratum. -/
theorem orderFortyNineStratumExcluded_one_of_structuralTerminals
    (hall : OneHighAllEvenSectorExcluded)
    (hhexagon : OneHighMateMissHexagonSectorExcluded)
    (hturn : OneHighThreePairTurnSectorExcluded)
    (hcross : OneHighCrossBlockSectorExcluded) :
    OrderFortyNineStratumExcluded 1 := by
  intro G _ _ _ hfree hmin hHigh
  have hnonempty : (orderFortyNineHighVertices G).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨v, hvMem⟩ := hnonempty
  have hv : G.degree v = 8 := by
    simpa [orderFortyNineHighVertices] using hvMem
  obtain ⟨p⟩ := orderFortyNine_exists_rawOneHighPresentationData
    G hfree hmin (Fintype.card_fin 49) hHigh hv
  rcases orderFortyNine_oneHigh_structural_sector_capstone
      G hfree hmin (Fintype.card_fin 49) hv p with
    heven | hmate | hthree | hfour
  · exact hall G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p heven
  · exact hhexagon G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hmate
  · exact hturn G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hthree
  · exact hcross G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hfour

end

end Erdos85
