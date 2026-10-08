import Proofs.Erdos85H5Fast

/-! Part 8 of the 16-way split five-high search, cell `t = 0` (`native_decide`). -/

namespace Erdos85
namespace H5

theorem cellPartF_0_4_16_08 : cellPartF 0 4 16 8 = true := by
  native_decide

end H5
end Erdos85
