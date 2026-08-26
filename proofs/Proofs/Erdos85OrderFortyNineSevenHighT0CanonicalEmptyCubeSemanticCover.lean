import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptySemanticOrbitCover
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSatisfaction
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeTerminal
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfTerminal

/-! # Assemble the canonical H7 empty-cube semantic cover -/

namespace Erdos85

/-- A semantic satisfiability theorem for the compact base CNF, together with
the checked empty-mask orbit consumer, supplies the terminal's exact semantic
cover interface. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticCover_of_baseSat
    (hbase : ∀ (H : SimpleGraph SevenHighT0CanonicalIndex)
      (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H →
        ∃ val : DimacsValuation,
          orderFortyNineSevenHighT0CanonicalSatCnf.Sat
              (satAssignmentOfDimacs val) ∧
            ∀ id, id ≤ 861 →
              val id = sevenHighT0CanonicalEdgeVal H id) :
    SevenHighT0CanonicalEmptyCubeSemanticCover := by
  intro H _ semantics
  obtain ⟨edgeCount, hedgeLow, hedgeHigh, typeIndex, htypeIndex,
      σ, relabeledSemantics, hmask⟩ :=
    semantics.exists_relabel_emptyRepresentative
  obtain ⟨val, hbaseSat, hedgeAgree⟩ :=
    hbase (sevenHighT0CanonicalRelabel σ H) inferInstance
      relabeledSemantics
  refine ⟨edgeCount, hedgeLow, hedgeHigh, typeIndex, htypeIndex,
    satAssignmentOfDimacs val, ?_⟩
  exact sevenHighT0CanonicalEmptyRepresentativeCube_sat
    (sevenHighT0CanonicalRelabel σ H) val edgeCount typeIndex
    hbaseSat hedgeAgree hmask

/-- Unconditional semantic coverage of the 43 checked H7 empty cubes. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticCover :
    SevenHighT0CanonicalEmptyCubeSemanticCover :=
  sevenHighT0CanonicalEmptyCubeSemanticCover_of_baseSat
    sevenHighT0CanonicalBaseSat

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticCover_of_baseSat
#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticCover
