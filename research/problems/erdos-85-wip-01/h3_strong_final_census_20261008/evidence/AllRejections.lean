import Rejection0
import Rejection1
import Rejection2
import Rejection3
import Rejection4
import Rejection5
import Rejection6
import Rejection7
import Rejection8
import Rejection9
import Rejection10
import Rejection11
import Rejection12
import Rejection13
import Rejection14
import Rejection15
import Rejection16
import Rejection17
import Rejection18
import Rejection19
import Rejection20
import Rejection21
import Rejection22
import Rejection23
import Rejection24
import Rejection25
import Rejection26
import Rejection27
import Rejection28
import Rejection29
import Rejection30
import Rejection31
import Rejection32
import Rejection33
import Rejection34
import Rejection35
import Rejection36
import Rejection37
import Rejection38
import Rejection39
import Rejection40
import Rejection41
import Rejection42
import Rejection43
import Rejection44
import Rejection45
import Rejection46
import Rejection47
import Rejection48
import Rejection49
import Rejection50
import Rejection51
import Rejection52
import Rejection53
import Rejection54
import Rejection55
import Rejection56
import Rejection57
import Rejection58
import Rejection59
import Rejection60
import Rejection61
import Rejection62
import Rejection63
import Rejection64
import Rejection65
import Rejection66
import Rejection67
import Rejection68
import Rejection69
namespace FixedPairAllRejections
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def cross : Fin 70 → Fin 16 → ThreeHighCross := ![Orbit0.cross,Orbit1.cross,Orbit2.cross,Orbit3.cross,Orbit4.cross,Orbit5.cross,Orbit6.cross,Orbit7.cross,Orbit8.cross,Orbit9.cross,Orbit10.cross,Orbit11.cross,Orbit12.cross,Orbit13.cross,Orbit14.cross,Orbit15.cross,Orbit16.cross,Orbit17.cross,Orbit18.cross,Orbit19.cross,Orbit20.cross,Orbit21.cross,Orbit22.cross,Orbit23.cross,Orbit24.cross,Orbit25.cross,Orbit26.cross,Orbit27.cross,Orbit28.cross,Orbit29.cross,Orbit30.cross,Orbit31.cross,Orbit32.cross,Orbit33.cross,Orbit34.cross,Orbit35.cross,Orbit36.cross,Orbit37.cross,Orbit38.cross,Orbit39.cross,Orbit40.cross,Orbit41.cross,Orbit42.cross,Orbit43.cross,Orbit44.cross,Orbit45.cross,Orbit46.cross,Orbit47.cross,Orbit48.cross,Orbit49.cross,Orbit50.cross,Orbit51.cross,Orbit52.cross,Orbit53.cross,Orbit54.cross,Orbit55.cross,Orbit56.cross,Orbit57.cross,Orbit58.cross,Orbit59.cross,Orbit60.cross,Orbit61.cross,Orbit62.cross,Orbit63.cross,Orbit64.cross,Orbit65.cross,Orbit66.cross,Orbit67.cross,Orbit68.cross,Orbit69.cross]
theorem no_joint (r : Fin 70) (g : Fin 16) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) (cross r g)) := by
  fin_cases r
  · exact Rejection0.no_joint g
  · exact Rejection1.no_joint g
  · exact Rejection2.no_joint g
  · exact Rejection3.no_joint g
  · exact Rejection4.no_joint g
  · exact Rejection5.no_joint g
  · exact Rejection6.no_joint g
  · exact Rejection7.no_joint g
  · exact Rejection8.no_joint g
  · exact Rejection9.no_joint g
  · exact Rejection10.no_joint g
  · exact Rejection11.no_joint g
  · exact Rejection12.no_joint g
  · exact Rejection13.no_joint g
  · exact Rejection14.no_joint g
  · exact Rejection15.no_joint g
  · exact Rejection16.no_joint g
  · exact Rejection17.no_joint g
  · exact Rejection18.no_joint g
  · exact Rejection19.no_joint g
  · exact Rejection20.no_joint g
  · exact Rejection21.no_joint g
  · exact Rejection22.no_joint g
  · exact Rejection23.no_joint g
  · exact Rejection24.no_joint g
  · exact Rejection25.no_joint g
  · exact Rejection26.no_joint g
  · exact Rejection27.no_joint g
  · exact Rejection28.no_joint g
  · exact Rejection29.no_joint g
  · exact Rejection30.no_joint g
  · exact Rejection31.no_joint g
  · exact Rejection32.no_joint g
  · exact Rejection33.no_joint g
  · exact Rejection34.no_joint g
  · exact Rejection35.no_joint g
  · exact Rejection36.no_joint g
  · exact Rejection37.no_joint g
  · exact Rejection38.no_joint g
  · exact Rejection39.no_joint g
  · exact Rejection40.no_joint g
  · exact Rejection41.no_joint g
  · exact Rejection42.no_joint g
  · exact Rejection43.no_joint g
  · exact Rejection44.no_joint g
  · exact Rejection45.no_joint g
  · exact Rejection46.no_joint g
  · exact Rejection47.no_joint g
  · exact Rejection48.no_joint g
  · exact Rejection49.no_joint g
  · exact Rejection50.no_joint g
  · exact Rejection51.no_joint g
  · exact Rejection52.no_joint g
  · exact Rejection53.no_joint g
  · exact Rejection54.no_joint g
  · exact Rejection55.no_joint g
  · exact Rejection56.no_joint g
  · exact Rejection57.no_joint g
  · exact Rejection58.no_joint g
  · exact Rejection59.no_joint g
  · exact Rejection60.no_joint g
  · exact Rejection61.no_joint g
  · exact Rejection62.no_joint g
  · exact Rejection63.no_joint g
  · exact Rejection64.no_joint g
  · exact Rejection65.no_joint g
  · exact Rejection66.no_joint g
  · exact Rejection67.no_joint g
  · exact Rejection68.no_joint g
  · exact Rejection69.no_joint g
end FixedPairAllRejections
#print axioms FixedPairAllRejections.no_joint
