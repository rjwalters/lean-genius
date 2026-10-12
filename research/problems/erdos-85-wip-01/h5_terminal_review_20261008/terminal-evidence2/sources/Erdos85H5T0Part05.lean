import Proofs.Erdos85H5Fast

/-! Part 5 of the 16-way split five-high search, cell `t = 0` (`native_decide`). -/

namespace Erdos85
namespace H5

theorem cellPartF_0_4_16_05 : cellPartF 0 4 16 5 = true := by
  native_decide

end H5
end Erdos85
