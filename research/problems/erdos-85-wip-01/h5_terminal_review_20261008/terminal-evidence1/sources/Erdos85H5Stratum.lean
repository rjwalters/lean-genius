import Proofs.Erdos85H5T0
import Proofs.Erdos85H5T1
import Proofs.Erdos85H5T2
import Proofs.Erdos85OrderFortyNineFiveHighTwoFiber

/-!
# Exclusion of the order-49 five-high stratum

The three canonical five-high representatives are excluded by the split
searches of `Erdos85H5T0`, `Erdos85H5T1`, `Erdos85H5T2`.  The existing graph
cover `fiveHighCanonicalGraphCover_all` lifts them to the three
`(h, t) = (5, t)` cells and to the stratum.

Besides the three standard axioms, the conclusions depend on the
`native_decide` axioms of the part theorems (16 + 16 + 8 for the stratum)
and on whatever the imported graph-cover development depends on; the exact
lists are printed below.
-/

namespace Erdos85
namespace H5

/-- The order-49 cell with five high vertices and no triple support. -/
theorem orderFortyNineTripleCellExcluded_five_zero :
    OrderFortyNineTripleCellExcluded 5 0 :=
  orderFortyNineTripleCellExcluded_five_of_canonical
    (fiveHighCanonicalGraphCover_all 0 (by omega))
    fiveHighCanonicalRepresentativeExcluded_0

/-- The order-49 cell with five high vertices and one triple support. -/
theorem orderFortyNineTripleCellExcluded_five_one :
    OrderFortyNineTripleCellExcluded 5 1 :=
  orderFortyNineTripleCellExcluded_five_of_canonical
    (fiveHighCanonicalGraphCover_all 1 (by omega))
    fiveHighCanonicalRepresentativeExcluded_1

/-- The order-49 cell with five high vertices and two triple supports. -/
theorem orderFortyNineTripleCellExcluded_five_two :
    OrderFortyNineTripleCellExcluded 5 2 :=
  orderFortyNineTripleCellExcluded_five_of_canonical
    (fiveHighCanonicalGraphCover_all 2 (by omega))
    fiveHighCanonicalRepresentativeExcluded_2

/-- The order-49 five-high stratum is excluded. -/
theorem orderFortyNineStratumExcluded_five : OrderFortyNineStratumExcluded 5 :=
  orderFortyNineStratumExcluded_five_of_representativeExclusions fun index hindex =>
    match index, hindex with
    | 0, _ => fiveHighCanonicalRepresentativeExcluded_0
    | 1, _ => fiveHighCanonicalRepresentativeExcluded_1
    | 2, _ => fiveHighCanonicalRepresentativeExcluded_2
    | n + 3, h => absurd h (by omega)

end H5
end Erdos85

#print axioms Erdos85.H5.orderFortyNineTripleCellExcluded_five_zero
#print axioms Erdos85.H5.orderFortyNineTripleCellExcluded_five_one
#print axioms Erdos85.H5.orderFortyNineTripleCellExcluded_five_two
#print axioms Erdos85.H5.orderFortyNineStratumExcluded_five
