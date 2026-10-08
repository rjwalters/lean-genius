import Proofs.Erdos85H5Bridge

/-! Part 1 of the 8-way split five-high search, cell `t = 2` (`native_decide`). -/

namespace Erdos85
namespace H5

theorem cellPart_2_12_8_01 : cellPart 2 12 8 1 = true := by
  native_decide

end H5
end Erdos85
