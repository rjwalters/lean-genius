import Proofs.Erdos85H5T0Part00
import Proofs.Erdos85H5T0Part01
import Proofs.Erdos85H5T0Part02
import Proofs.Erdos85H5T0Part03
import Proofs.Erdos85H5T0Part04
import Proofs.Erdos85H5T0Part05
import Proofs.Erdos85H5T0Part06
import Proofs.Erdos85H5T0Part07
import Proofs.Erdos85H5T0Part08
import Proofs.Erdos85H5T0Part09
import Proofs.Erdos85H5T0Part10
import Proofs.Erdos85H5T0Part11
import Proofs.Erdos85H5T0Part12
import Proofs.Erdos85H5T0Part13
import Proofs.Erdos85H5T0Part14
import Proofs.Erdos85H5T0Part15

/-!
# Exclusion of the canonical five-high representative `t = 0`

Composition of the 16 `native_decide` parts of the split search with the
kernel-checked engine soundness and bridge.  Besides the three standard
axioms, the conclusion depends on exactly the 16 axioms that
`native_decide` emits for the part theorems `cellPartF_0_4_16_NN` (trust
in compiled evaluation of `cellPartF 0 4 16 NN`).
-/

namespace Erdos85
namespace H5

theorem cellPartF_0_4_16_all : ∀ r, r < 16 → cellPartF 0 4 16 r = true
  | 0, _ => cellPartF_0_4_16_00
  | 1, _ => cellPartF_0_4_16_01
  | 2, _ => cellPartF_0_4_16_02
  | 3, _ => cellPartF_0_4_16_03
  | 4, _ => cellPartF_0_4_16_04
  | 5, _ => cellPartF_0_4_16_05
  | 6, _ => cellPartF_0_4_16_06
  | 7, _ => cellPartF_0_4_16_07
  | 8, _ => cellPartF_0_4_16_08
  | 9, _ => cellPartF_0_4_16_09
  | 10, _ => cellPartF_0_4_16_10
  | 11, _ => cellPartF_0_4_16_11
  | 12, _ => cellPartF_0_4_16_12
  | 13, _ => cellPartF_0_4_16_13
  | 14, _ => cellPartF_0_4_16_14
  | 15, _ => cellPartF_0_4_16_15
  | n + 16, h => absurd h (by omega)

/-- The canonical five-high representative with `0` triple supports is
excluded. -/
theorem fiveHighCanonicalRepresentativeExcluded_0 :
    FiveHighCanonicalRepresentativeExcluded 0 :=
  fiveHighCanonicalRepresentativeExcluded_of_partsF 0 4 16 (by norm_num)
    cellPartF_0_4_16_all

end H5
end Erdos85

#print axioms Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_0
