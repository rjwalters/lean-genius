import Proofs.Erdos85H3PairCell
import Proofs.Erdos85H3TripleCompletionCell
import Proofs.Erdos85OrderFortyNineStrataCapstone

/- The two native-backed cells cover the entire three-high stratum. -/
namespace Erdos85
namespace H3

theorem orderFortyNineStratumExcluded_three : OrderFortyNineStratumExcluded 3 :=
  orderFortyNineStratumExcluded_three_of_tripleCells
    H3Pair.orderFortyNineTripleCellExcluded_three_zero
    H3TripleCompletion.orderFortyNineTripleCellExcluded_three_one

end H3
end Erdos85

#print axioms Erdos85.H3.orderFortyNineStratumExcluded_three
