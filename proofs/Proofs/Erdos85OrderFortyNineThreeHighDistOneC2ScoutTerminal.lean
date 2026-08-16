import Proofs.Erdos85OrderFortyNineThreeHighScoutGraphBridge

/-!
# Terminal socket for the three-high distance-one scout

This module keeps the structural normalization and the independently checked
LRAT certificate decoupled.  The normalization lane only has to produce the
existing graph-facing aligned-labeling predicate; once the certificate lane
supplies a checker result, the candidate graph is impossible.
-/

namespace Erdos85

open SimpleGraph

/-- Certificate payload for the exact `dist1_c2` scout CNF. -/
structure ThreeHighDistOneC2ScoutCertificate where
  proof : Array Std.Tactic.BVDecide.LRAT.IntAction
  checked : Std.Tactic.BVDecide.LRAT.check proof
    orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf

/-- Final composition point between the graph normalization and certificate
lanes for the surviving distinct-common-neighbor three-high geometry. -/
theorem false_of_exists_threeHighDistOneC2ScoutAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (haligned : ∃ E : Equiv.Perm (Fin 49),
      ThreeHighDistOneC2ScoutAlignedLabeling G E)
    (certificate : ThreeHighDistOneC2ScoutCertificate) : False := by
  obtain ⟨E, hE⟩ := haligned
  exact false_of_threeHighDistOneC2ScoutAlignedLabeling_lrat
    G hfree E hE certificate.proof certificate.checked

end Erdos85
