import Proofs.Erdos85H3TripleCompletionSplit

/- A traversal diagnostic, not a graph-exclusion theorem. Every phase-one
leaf is accepted without running phases two or three. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos85.H3TripleCompletion

theorem phaseOneTraversal : dfs1 (fun _ => true) 70 s0 = true := by native_decide

end Erdos85.H3TripleCompletion

#print axioms Erdos85.H3TripleCompletion.phaseOneTraversal
