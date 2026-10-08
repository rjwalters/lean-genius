import Proofs.Erdos85H3TripleCompletionSplit

/- One bounded diagnostic part; this file does not exclude the whole cell. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos85.H3TripleCompletion

theorem triplePart_384_0 : triplePart 384 0 = true := by native_decide

end Erdos85.H3TripleCompletion

#print axioms Erdos85.H3TripleCompletion.triplePart_384_0
