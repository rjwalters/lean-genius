import Proofs.Erdos85H5T2Part00
import Proofs.Erdos85H5T2Part01
import Proofs.Erdos85H5T2Part02
import Proofs.Erdos85H5T2Part03
import Proofs.Erdos85H5T2Part04
import Proofs.Erdos85H5T2Part05
import Proofs.Erdos85H5T2Part06
import Proofs.Erdos85H5T2Part07

/-!
# Exclusion of the canonical five-high representative `t = 2`

Composition of the 8 `native_decide` parts of the split search with the
kernel-checked engine soundness and bridge.  Besides the three standard
axioms, the conclusion depends on exactly the 8 axioms that
`native_decide` emits for the part theorems `cellPart_2_12_8_NN` (trust
in compiled evaluation of `cellPart 2 12 8 NN`).
-/

namespace Erdos85
namespace H5

theorem cellPart_2_12_8_all : ∀ r, r < 8 → cellPart 2 12 8 r = true
  | 0, _ => cellPart_2_12_8_00
  | 1, _ => cellPart_2_12_8_01
  | 2, _ => cellPart_2_12_8_02
  | 3, _ => cellPart_2_12_8_03
  | 4, _ => cellPart_2_12_8_04
  | 5, _ => cellPart_2_12_8_05
  | 6, _ => cellPart_2_12_8_06
  | 7, _ => cellPart_2_12_8_07
  | n + 8, h => absurd h (by omega)

/-- The canonical five-high representative with `2` triple supports is
excluded. -/
theorem fiveHighCanonicalRepresentativeExcluded_2 :
    FiveHighCanonicalRepresentativeExcluded 2 :=
  fiveHighCanonicalRepresentativeExcluded_of_parts 2 12 8 (by norm_num)
    cellPart_2_12_8_all

end H5
end Erdos85

#print axioms Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_2
