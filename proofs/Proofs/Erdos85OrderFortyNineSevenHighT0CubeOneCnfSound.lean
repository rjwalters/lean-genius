import Proofs.Erdos85OrderFortyNineSevenHighT0CubeCnfSound
import Proofs.Erdos85OrderFortyNineT0TwoCubeBridge

/-!
# Closed encoding-soundness socket for the reduced seven-high cube

Cube zero is structurally impossible in the two-cube bridge.  This module
packages the verified generator semantics for cube one as the exact remaining
encoding hypothesis consumed by that bridge.
-/

namespace Erdos85

theorem sevenHighT0CubeOneCnfSound_proved :
    SevenHighT0CubeOneCnfSound := by
  intro edges h
  exact orderFortyNineGeneratedH7T0CubeSatCnf_sat_of_relationCore h

end Erdos85
