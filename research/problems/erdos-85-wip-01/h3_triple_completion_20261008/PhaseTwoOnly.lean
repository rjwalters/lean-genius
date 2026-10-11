import Proofs.Erdos85H3TripleCompletionSplit

/- A traversal diagnostic for bucket 384/0, not graph exclusion. It keeps
the original phase-one hash selection and accepts all phase-two leaves. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos85.H3TripleCompletion

theorem phaseTwoTraversal :
    dfs1 (fun s => decide (stKey s % 384 ≠ 0) ||
      dfs2 (fun _ => true) 30 s allTriples) 70 s0 = true := by native_decide

end Erdos85.H3TripleCompletion

#print axioms Erdos85.H3TripleCompletion.phaseTwoTraversal
