import Proofs.Erdos85OneHighGraphPairingRefinement
import Proofs.Erdos85OneHighKnownSectorParity

/-! # Known parity sectors for the graph-induced pairing refinement -/

namespace Erdos85

noncomputable section

/-- Universal compact parity-state coverage of the graph's relevant miss table
applies to the particular pairing refinement induced by the graph. -/
theorem oneHighGraphPairingRefinement_hasKnownParitySector
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hcovered :
      oneHighTableKnownParitySectorsCoveredByParity p.profile
        (oneHighGraphRelevantMissTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
          p.profile) = true) :
    oneHighRefinementHasKnownParitySector
        (oneHighGraphPairingRefinement G hfree hv p) = true := by
  rw [oneHighTableKnownParitySectorsCoveredByParity_eq] at hcovered
  exact oneHighTableKnownParitySectorsCovered_sound hcovered
    (oneHighGraphPairingRefinement_mem G hfree hv p)

/-- Equivalent compact-mask form of the graph-induced known-sector result. -/
theorem oneHighGraphPairingParityMask_hasKnownSector
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hcovered :
      oneHighTableKnownParitySectorsCoveredByParity p.profile
        (oneHighGraphRelevantMissTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
          p.profile) = true) :
    oneHighParityMaskHasKnownSector
        (oneHighPairingRefinementParityMask
          (oneHighGraphPairingRefinement G hfree hv p)) = true := by
  rw [oneHighParityMask_knownSector_refinement]
  exact oneHighGraphPairingRefinement_hasKnownParitySector
    G hfree hv p hcovered

end

end Erdos85
