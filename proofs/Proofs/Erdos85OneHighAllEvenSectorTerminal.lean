import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighExchangedMissCounting

/-! # Reduction of the one-high all-even terminal -/

namespace Erdos85

noncomputable section

/-- If every exchanged key has even multiplicity, then the total number of
nonconstant matching edges is even. -/
theorem even_nonconstantMatchingEdgeSources_of_all_exchanged_even
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L)
    (heven : ∀ key ∈ exchangedMissPairKeys L,
      Even (exchangedMissPairMultiplicity mate label key)) :
    Even (nonconstantMatchingEdgeSources mate label).card := by
  rw [← sum_exchangedMissPairMultiplicity_over_keys mate label]
  exact Finset.even_sum _ fun key hkey => heven key hkey

/-- The all-even terminal is reduced to the graph-side assertion that the
global nonconstant matching-edge count is odd. -/
theorem oneHighAllEvenSectorExcluded_of_global_nonconstant_odd
    (hodd : ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
      (_ : DecidableRel (antipodalGraph G).Adj)
      (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
      (hfree : ¬ containsC4 (Fin 49) G) →
      (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
      (hHigh : (orderFortyNineHighVertices G).card = 1) →
      ∀ {v : Fin 49} (hv : G.degree v = 8)
        (p : OneHighRawV2Presentation G hfree v),
        Odd (nonconstantMatchingEdgeSources
          (oneHighGlobalInternalMate G hfree v)
          (fun x => p.branchLabel
            (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
              p.mate p.mate_adj x))).card) :
    OneHighAllEvenSectorExcluded := by
  intro G _ _ _ hfree hmin hHigh v hv p
  dsimp only
  intro heven
  let mate := oneHighGlobalInternalMate G hfree v
  let label := fun x => p.branchLabel
    (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj x)
  have hcardEven : Even (nonconstantMatchingEdgeSources mate label).card :=
    even_nonconstantMatchingEdgeSources_of_all_exchanged_even mate label heven
  have hcardOdd : Odd (nonconstantMatchingEdgeSources mate label).card :=
    hodd G inferInstance inferInstance inferInstance hfree hmin hHigh hv p
  exact (Nat.not_even_iff_odd.mpr hcardOdd) hcardEven

end

end Erdos85
