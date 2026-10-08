import Proofs.Erdos85H3PairBridge

/-!
# The certified pair-cell search

`native_decide` evaluates the three-phase engine search on the initial
partial graph.  This is the only finite computation in the pair-cell
exclusion; it depends on `Lean.ofReduceBool`.
-/

namespace Erdos85
namespace H3Pair

set_option maxRecDepth 100000 in
theorem pairSearch_true : pairSearch = true := by
  native_decide

/-- The canonical `t = 0` three-high representative is excluded. -/
theorem threeHighCanonicalRepresentativeExcluded_zero :
    ThreeHighCanonicalRepresentativeExcluded 0 :=
  threeHighCanonicalRepresentativeExcluded_zero_of_pairSearch pairSearch_true

/-- The order-49 three-high pair cell `(h, t) = (3, 0)` is excluded. -/
theorem orderFortyNineTripleCellExcluded_three_zero :
    OrderFortyNineTripleCellExcluded 3 0 :=
  orderFortyNineTripleCellExcluded_three_zero_of_pairSearch pairSearch_true

end H3Pair
end Erdos85

#print axioms Erdos85.H3Pair.pairSearch_true
#print axioms Erdos85.H3Pair.threeHighCanonicalRepresentativeExcluded_zero
#print axioms Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero
