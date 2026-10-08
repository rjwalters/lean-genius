import Proofs.Erdos85H3PairSplit

/-! Part 8 of the 24-way split pair-cell search (`native_decide`). -/

namespace Erdos85
namespace H3Pair

theorem pairPart_24_08 : pairPart 24 8 = true := by
  native_decide

end H3Pair
end Erdos85
