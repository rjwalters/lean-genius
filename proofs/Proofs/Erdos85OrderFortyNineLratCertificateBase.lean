import Proofs.Erdos85DimacsSatBridge
import Proofs.Erdos85OrderFortyNineProfileMasks

namespace Erdos85

open Std.Tactic.BVDecide

/-- Pure parser used by every embedded order-49 LRAT certificate.  Falling
back to the empty proof is fail-safe: the subsequent positive `LRAT.check`
theorem cannot close if parsing fails. -/
def parseOrderFortyNineLratProof (text : String) : Array LRAT.IntAction :=
  match LRAT.parseLRATProof text.toUTF8 with
  | .ok proof => proof
  | .error _ => #[]

end Erdos85
