import Proofs.Erdos85OrderFortyNineThreeHighScoutGraphBridge

/-!
# Terminal sockets for the `b1` and `c1` three-high scouts

The graph-normalization and certificate lanes meet only here.  Each payload
contains an LRAT trace together with the kernel check for the exact generated
CNF; no trust is placed in the external SAT solver.
-/

namespace Erdos85

open SimpleGraph

structure ThreeHighDistOneB1ScoutCertificate where
  proof : Array Std.Tactic.BVDecide.LRAT.IntAction
  checked : Std.Tactic.BVDecide.LRAT.check proof
    orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf

structure ThreeHighDistOneC1ScoutCertificate where
  proof : Array Std.Tactic.BVDecide.LRAT.IntAction
  checked : Std.Tactic.BVDecide.LRAT.check proof
    orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf

structure ThreeHighDistOneNoCoincidenceScoutCertificates where
  b1 : ThreeHighDistOneB1ScoutCertificate
  c1 : ThreeHighDistOneC1ScoutCertificate

theorem false_of_exists_threeHighDistOneB1ScoutAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (haligned : ∃ E : Equiv.Perm (Fin 49),
      ThreeHighDistOneB1ScoutAlignedLabeling G E)
    (certificate : ThreeHighDistOneB1ScoutCertificate) : False := by
  obtain ⟨E, hE⟩ := haligned
  exact false_of_threeHighDistOneB1ScoutAlignedLabeling_lrat
    G hfree E hE certificate.proof certificate.checked

theorem false_of_exists_threeHighDistOneC1ScoutAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (haligned : ∃ E : Equiv.Perm (Fin 49),
      ThreeHighDistOneC1ScoutAlignedLabeling G E)
    (certificate : ThreeHighDistOneC1ScoutCertificate) : False := by
  obtain ⟨E, hE⟩ := haligned
  exact false_of_threeHighDistOneC1ScoutAlignedLabeling_lrat
    G hfree E hE certificate.proof certificate.checked

end Erdos85
