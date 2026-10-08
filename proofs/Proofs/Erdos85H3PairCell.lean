import Proofs.Erdos85H3PairPart00
import Proofs.Erdos85H3PairPart01
import Proofs.Erdos85H3PairPart02
import Proofs.Erdos85H3PairPart03
import Proofs.Erdos85H3PairPart04
import Proofs.Erdos85H3PairPart05
import Proofs.Erdos85H3PairPart06
import Proofs.Erdos85H3PairPart07
import Proofs.Erdos85H3PairPart08
import Proofs.Erdos85H3PairPart09
import Proofs.Erdos85H3PairPart10
import Proofs.Erdos85H3PairPart11
import Proofs.Erdos85H3PairPart12
import Proofs.Erdos85H3PairPart13
import Proofs.Erdos85H3PairPart14
import Proofs.Erdos85H3PairPart15
import Proofs.Erdos85H3PairPart16
import Proofs.Erdos85H3PairPart17
import Proofs.Erdos85H3PairPart18
import Proofs.Erdos85H3PairPart19
import Proofs.Erdos85H3PairPart20
import Proofs.Erdos85H3PairPart21
import Proofs.Erdos85H3PairPart22
import Proofs.Erdos85H3PairPart23

/-!
# Exclusion of the order-49 three-high pair cell

Composition of the 24 `native_decide` parts of the pair-cell search with
the kernel-checked engine soundness and bridge.  The result depends on
`Lean.ofReduceBool` through the 24 part theorems and on nothing else
beyond the standard axioms.
-/

namespace Erdos85
namespace H3Pair

theorem pairPart_24_all : ∀ r, r < 24 → pairPart 24 r = true
  | 0, _ => pairPart_24_00
  | 1, _ => pairPart_24_01
  | 2, _ => pairPart_24_02
  | 3, _ => pairPart_24_03
  | 4, _ => pairPart_24_04
  | 5, _ => pairPart_24_05
  | 6, _ => pairPart_24_06
  | 7, _ => pairPart_24_07
  | 8, _ => pairPart_24_08
  | 9, _ => pairPart_24_09
  | 10, _ => pairPart_24_10
  | 11, _ => pairPart_24_11
  | 12, _ => pairPart_24_12
  | 13, _ => pairPart_24_13
  | 14, _ => pairPart_24_14
  | 15, _ => pairPart_24_15
  | 16, _ => pairPart_24_16
  | 17, _ => pairPart_24_17
  | 18, _ => pairPart_24_18
  | 19, _ => pairPart_24_19
  | 20, _ => pairPart_24_20
  | 21, _ => pairPart_24_21
  | 22, _ => pairPart_24_22
  | 23, _ => pairPart_24_23
  | n + 24, h => absurd h (by omega)

/-- The canonical `t = 0` three-high representative is excluded. -/
theorem threeHighCanonicalRepresentativeExcluded_zero :
    ThreeHighCanonicalRepresentativeExcluded 0 :=
  threeHighCanonicalRepresentativeExcluded_zero_of_parts 24 (by norm_num) pairPart_24_all

/-- The order-49 three-high pair cell `(h, t) = (3, 0)` is excluded. -/
theorem orderFortyNineTripleCellExcluded_three_zero :
    OrderFortyNineTripleCellExcluded 3 0 :=
  orderFortyNineTripleCellExcluded_three_zero_of_parts 24 (by norm_num) pairPart_24_all

end H3Pair
end Erdos85

#print axioms Erdos85.H3Pair.threeHighCanonicalRepresentativeExcluded_zero
#print axioms Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero
