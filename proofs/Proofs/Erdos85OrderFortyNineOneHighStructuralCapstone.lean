import Proofs.Erdos85OneHighGraphStructuralCapstone
import Proofs.Erdos85OrderFortyNineStratification

/-! # Order-49 specialization of the one-high structural capstone -/

namespace Erdos85

noncomputable section

/-- At order 49 and minimum degree seven, the standard degree-eight
stratification supplies the tight-neighbor and local-matching hypotheses of
the structural sector capstone automatically. -/
theorem orderFortyNine_oneHigh_structural_sector_capstone
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) :
    let m := exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (fun x => p.branchLabel
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj x))
    (∀ key ∈ exchangedMissPairKeys (Fin 8), Even (m key)) ∨
      Nonempty (OneHighMateMissHexagon G v) ∨
      OneHighOddSupportThreePairTurnProp m ∨
      OneHighOddSupportCrossBlockProp m := by
  apply oneHighGraph_structural_sector_capstone G hfree hv
  · intro y hy
    exact orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv hy
  · exact orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
      G hfree hmin hcard hv

end

end Erdos85
