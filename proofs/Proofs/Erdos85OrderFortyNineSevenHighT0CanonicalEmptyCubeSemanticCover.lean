import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptySemanticOrbitCover
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSatisfaction
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeTerminal

/-! # Assemble the canonical H7 empty-cube semantic cover -/

namespace Erdos85

/-- A semantic satisfiability theorem for the compact base CNF, together with
the checked empty-mask orbit consumer, supplies the terminal's exact semantic
cover interface. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticCover_of_baseSat
    (hbase : ∀ (H : SimpleGraph SevenHighT0CanonicalIndex)
      (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H →
        orderFortyNineSevenHighT0CanonicalSatCnf.Sat
          (sevenHighT0CanonicalEdgeVal H)) :
    SevenHighT0CanonicalEmptyCubeSemanticCover := by
  intro H _ semantics
  obtain ⟨edgeCount, hedgeLow, hedgeHigh, typeIndex, htypeIndex,
      σ, relabeledSemantics, hmask⟩ :=
    semantics.exists_relabel_emptyRepresentative
  refine ⟨edgeCount, hedgeLow, hedgeHigh, typeIndex, htypeIndex,
    sevenHighT0CanonicalEdgeVal (sevenHighT0CanonicalRelabel σ H), ?_⟩
  exact sevenHighT0CanonicalEmptyRepresentativeCube_sat
    (sevenHighT0CanonicalRelabel σ H) edgeCount typeIndex
    (hbase (sevenHighT0CanonicalRelabel σ H) inferInstance
      relabeledSemantics) hmask

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticCover_of_baseSat
