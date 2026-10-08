import Proofs.Erdos85H3PairSplit

/-! Timing probe only: a few phase-1 leaves of the pair-cell search. -/

namespace Erdos85
namespace H3Pair

theorem pairBench_a : pairPart 1448 7 = true := by
  native_decide

theorem pairBench_b : pairPart 1448 8 = true := by
  native_decide

theorem pairBench_c : pairPart 1448 9 = true := by
  native_decide

end H3Pair
end Erdos85
