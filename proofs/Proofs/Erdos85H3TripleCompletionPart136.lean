import Proofs.Erdos85H3TripleCompletionSplit

/- Part 136 of the 384-way completion search. Requires native evaluation. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos85.H3TripleCompletion

theorem triplePart_384_136 : triplePart 384 136 = true := by
  native_decide

end Erdos85.H3TripleCompletion

#print axioms Erdos85.H3TripleCompletion.triplePart_384_136
