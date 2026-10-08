import Proofs.Erdos85H3PairSplit

/-! Part 6 of the 24-way split pair-cell search (`native_decide`). -/

namespace Erdos85
namespace H3Pair

theorem pairPart_24_06 : pairPart 24 6 = true := by
  native_decide

end H3Pair
end Erdos85
