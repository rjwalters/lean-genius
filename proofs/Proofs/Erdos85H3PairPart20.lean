import Proofs.Erdos85H3PairSplit

/-! Part 20 of the 24-way split pair-cell search (`native_decide`). -/

namespace Erdos85
namespace H3Pair

theorem pairPart_24_20 : pairPart 24 20 = true := by
  native_decide

end H3Pair
end Erdos85
