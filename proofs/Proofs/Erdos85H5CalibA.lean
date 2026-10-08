import Proofs.Erdos85H5Bridge

/-! Timing probe (temporary): one small part of the T2 search. -/

namespace Erdos85
namespace H5

theorem calibA : cellPart 2 4 8 2 = true := by
  native_decide

end H5
end Erdos85
