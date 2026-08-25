import Proofs.Erdos85OrderFortyNineSevenHighT0CubeOneCnfSound
import Proofs.Erdos85OrderFortyNineT0TwoCubeBridge

/-!
# Certificate-only endpoint for the reduced seven-high zero-fiber stratum

Encoding soundness for cube one is now internal.  Cube zero is structurally
impossible, so the sole remaining input to this endpoint is a checked LRAT
refutation of the generated cube-one CNF.
-/

namespace Erdos85

open Std.Tactic.BVDecide

theorem sevenHighT0_canonicalExcluded_of_cubeOne_lratCheck_provedSound
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof
      (orderFortyNineGeneratedH7T0CubeSatCnf 1)) :
    SevenHighCanonicalRepresentativeExcluded 0 0 :=
  sevenHighT0_canonicalExcluded_of_cubeOne_lratCheck
    sevenHighT0CubeOneCnfSound_proved proof hcheck

end Erdos85
