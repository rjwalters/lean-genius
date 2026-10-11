import Proofs.Erdos85H3PairSplit

/-! Part 0 of the 24-way split pair-cell search (`native_decide`). -/

namespace Erdos85
namespace H3Pair

theorem pairPart_24_00 : pairPart 24 0 = true := by
  native_decide

end H3Pair
end Erdos85
