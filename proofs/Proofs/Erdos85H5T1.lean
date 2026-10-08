import Proofs.Erdos85H5T1Part00
import Proofs.Erdos85H5T1Part01
import Proofs.Erdos85H5T1Part02
import Proofs.Erdos85H5T1Part03
import Proofs.Erdos85H5T1Part04
import Proofs.Erdos85H5T1Part05
import Proofs.Erdos85H5T1Part06
import Proofs.Erdos85H5T1Part07
import Proofs.Erdos85H5T1Part08
import Proofs.Erdos85H5T1Part09
import Proofs.Erdos85H5T1Part10
import Proofs.Erdos85H5T1Part11
import Proofs.Erdos85H5T1Part12
import Proofs.Erdos85H5T1Part13
import Proofs.Erdos85H5T1Part14
import Proofs.Erdos85H5T1Part15

/-!
# Exclusion of the canonical five-high representative `t = 1`

Composition of the 16 `native_decide` parts of the split search with the
kernel-checked engine soundness and bridge.  Besides the three standard
axioms, the conclusion depends on exactly the 16 axioms that
`native_decide` emits for the part theorems `cellPartF_1_6_16_NN` (trust
in compiled evaluation of `cellPartF 1 6 16 NN`).
-/

namespace Erdos85
namespace H5

theorem cellPartF_1_6_16_all : ∀ r, r < 16 → cellPartF 1 6 16 r = true
  | 0, _ => cellPartF_1_6_16_00
  | 1, _ => cellPartF_1_6_16_01
  | 2, _ => cellPartF_1_6_16_02
  | 3, _ => cellPartF_1_6_16_03
  | 4, _ => cellPartF_1_6_16_04
  | 5, _ => cellPartF_1_6_16_05
  | 6, _ => cellPartF_1_6_16_06
  | 7, _ => cellPartF_1_6_16_07
  | 8, _ => cellPartF_1_6_16_08
  | 9, _ => cellPartF_1_6_16_09
  | 10, _ => cellPartF_1_6_16_10
  | 11, _ => cellPartF_1_6_16_11
  | 12, _ => cellPartF_1_6_16_12
  | 13, _ => cellPartF_1_6_16_13
  | 14, _ => cellPartF_1_6_16_14
  | 15, _ => cellPartF_1_6_16_15
  | n + 16, h => absurd h (by omega)

/-- The canonical five-high representative with `1` triple supports is
excluded. -/
theorem fiveHighCanonicalRepresentativeExcluded_1 :
    FiveHighCanonicalRepresentativeExcluded 1 :=
  fiveHighCanonicalRepresentativeExcluded_of_partsF 1 6 16 (by norm_num)
    cellPartF_1_6_16_all

end H5
end Erdos85

#print axioms Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_1
