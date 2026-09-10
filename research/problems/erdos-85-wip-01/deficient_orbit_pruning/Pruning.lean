import Deficient_3_3_0
import Proofs.Erdos85ThreeHighDeficientLowDegreeTable
import Proofs.Erdos85ThreeHighTriangleTables
import Proofs.Erdos85ThreeHighDeficientPairTable
import Proofs.Erdos85ThreeHighDeficientExternalFarTable
import Proofs.Erdos85ThreeHighDeficientFarColorTable
import Proofs.Erdos85ThreeHighDeficientLowAdjacentTable
import Proofs.Erdos85ThreeHighDeficientExternalSignedFarTable
import Proofs.Erdos85ThreeHighSecondaryDegreeClasses

namespace DeficientUOrbitPruning
open Erdos85
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
attribute [local irreducible] threeHighCrossDomain

def representative := DeficientUShard_3_3_0.representative
def parameters (r : Fin 370) : ThreeBlockDeficientFirstRowParameters :=
  threeBlockDeficientCompactCode (DeficientUShard_3_3_0.repA r)
    (DeficientUShard_3_3_0.repB r) (DeficientUShard_3_3_0.repP r) (DeficientUShard_3_3_0.repD r)

def lowMap : Fin 15 → Fin 370 := ![6,45,63,80,98,131,148,155,195,222,229,276,293,329,363]
theorem low_parameters (i : Fin 15) : parameters (lowMap i) = threeHighDeficientLowDegreeTable i := by
  decide +revert
theorem low_adj (i : Fin 15) : representative (lowMap i) = threeHighDeficientLowDegreeTableAdj i := by
  change threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (parameters (lowMap i))) = _
  rw [low_parameters]
  rfl
def lowCodes : Finset (Fin 370) := Finset.univ.image lowMap

def triangleMap : Fin 35 → Fin 370 := ![4,5,27,56,79,86,110,125,126,128,134,136,141,145,152,157,158,161,187,189,198,209,223,226,231,232,240,254,260,261,278,283,301,309,325]
theorem triangle_parameters (i : Fin 35) : parameters (triangleMap i) = threeHighDeficientTriangleTable i := by
  decide +revert
theorem triangle_adj (i : Fin 35) : representative (triangleMap i) = threeHighDeficientTriangleTableAdj i := by
  change threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (parameters (triangleMap i))) = _
  rw [triangle_parameters]
  rfl
def triangleCodes : Finset (Fin 370) := Finset.univ.image triangleMap

def pairMap : Fin 41 → Fin 370 := ![9,12,23,31,49,57,58,83,88,90,104,112,127,137,139,142,144,159,160,164,165,168,179,183,191,200,205,233,236,238,249,257,270,284,294,297,299,320,334,337,340]
theorem pair_parameters (i : Fin 41) : parameters (pairMap i) = threeHighDeficientPairTable i := by
  decide +revert
theorem pair_adj (i : Fin 41) : representative (pairMap i) = threeHighDeficientPairTableAdj i := by
  change threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (parameters (pairMap i))) = _
  rw [pair_parameters]
  rfl
def pairCodes : Finset (Fin 370) := Finset.univ.image pairMap

def externalMap : Fin 51 → Fin 370 := ![3,7,11,13,20,21,29,41,46,48,61,64,81,85,87,94,105,111,114,132,138,143,149,163,167,170,172,181,184,186,190,203,206,207,224,237,239,243,244,245,248,251,259,264,269,272,295,298,310,342,344]
theorem external_parameters (i : Fin 51) : parameters (externalMap i) = threeHighDeficientExternalFarTable i := by
  decide +revert
theorem external_adj (i : Fin 51) : representative (externalMap i) = threeHighDeficientExternalFarAdj i := by
  change threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (parameters (externalMap i))) = _
  rw [external_parameters]
  rfl
def externalCodes : Finset (Fin 370) := Finset.univ.image externalMap

def farMap : Fin 89 → Fin 370 := ![0,1,2,3,7,8,10,11,13,14,15,16,17,18,19,22,25,28,29,30,33,36,41,42,43,44,47,54,55,59,60,61,62,64,66,67,71,74,77,78,81,82,84,85,87,89,92,94,95,96,97,100,103,108,109,111,116,121,123,124,129,130,133,135,146,147,153,154,156,163,166,169,188,206,227,228,230,239,243,250,259,271,277,282,298,308,330,344,355]
theorem far_parameters (i : Fin 89) : parameters (farMap i) = threeHighDeficientFarColorTable i := by
  decide +revert
theorem far_adj (i : Fin 89) : representative (farMap i) = threeHighDeficientFarColorTableAdj i := by
  change threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (parameters (farMap i))) = _
  rw [far_parameters]
  rfl
def farCodes : Finset (Fin 370) := Finset.univ.image farMap

def adjacentMap : Fin 8 → Fin 370 := ![24,38,50,65,72,106,117,119]
theorem adjacent_parameters (i : Fin 8) : parameters (adjacentMap i) = threeHighDeficientLowAdjacentTable i := by
  decide +revert
theorem adjacent_adj (i : Fin 8) : representative (adjacentMap i) = threeHighDeficientLowAdjacentAdj i := by
  change threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (parameters (adjacentMap i))) = _
  rw [adjacent_parameters]
  rfl
def adjacentCodes : Finset (Fin 370) := Finset.univ.image adjacentMap

def signedMap : Fin 13 → Fin 370 := ![32,34,91,102,216,274,327,328,332,349,352,357,361]
theorem signed_parameters (i : Fin 13) : parameters (signedMap i) = threeHighDeficientExternalSignedFarTable i := by
  decide +revert
theorem signed_adj (i : Fin 13) : representative (signedMap i) = threeHighDeficientExternalSignedFarAdj i := by
  change threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (parameters (signedMap i))) = _
  rw [signed_parameters]
  rfl
def signedCodes : Finset (Fin 370) := Finset.univ.image signedMap

def excludedCodes : Finset (Fin 370) := lowCodes ∪ triangleCodes ∪ pairCodes ∪ externalCodes
def conditionalCodes : Finset (Fin 370) := farCodes ∪ adjacentCodes ∪ signedCodes
def farRCodes : Finset (Fin 21) := {0,1,11}
def remainingPairs : Finset (Fin 370 × Fin 21) :=
  ((Finset.univ \ excludedCodes).product (threeHighSecondaryDegreeCodes 6)) \
    (conditionalCodes.product farRCodes)

theorem far_R_checked (q : Fin 21) (hq : q ∈ farRCodes) :
    threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q) 6 7 = true ∧
    threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q) 7 6 = true := by
  decide +revert
theorem remainingPairs_card : remainingPairs.card = 1554 := by
  rw [remainingPairs,threeHighSecondaryDegreeCodes_six]
  decide

theorem excluded_no_external (r : Fin 370) (hr : r ∈ excludedCodes)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (representative r) R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (representative r) R cross)
      threeHighCanonicalRow = true) : False := by
  simp only [excludedCodes,Finset.mem_union] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    rw [low_adj] at hc
    exact threeHighDeficientLowDegreeTable_no_cross i R cross hc
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    rw [triangle_adj] at hc
    exact threeHighDeficientTriangleTable_no_cross i R cross hc
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    rw [pair_adj] at hc
    exact threeHighDeficientPairTable_no_cross i R cross hc
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    rw [external_adj] at hc hExt
    exact threeHighDeficientExternalFarTable_no_external_cross i R cross hc hExt

theorem conditional_no_external (r : Fin 370) (hr : r ∈ conditionalCodes)
    (R : Fin 8 → Fin 8 → Bool) (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain (representative r) R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (representative r) R cross)
      threeHighCanonicalRow = true) : False := by
  simp only [conditionalCodes,Finset.mem_union] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    rw [far_adj] at hc
    exact threeHighDeficientFarColorTable_no_cross i R h67 h76 cross hc
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    rw [adjacent_adj] at hc
    exact threeHighDeficientLowAdjacentTable_no_cross i R h67 h76 cross hc
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    rw [signed_adj] at hc hExt
    exact threeHighDeficientExternalSignedFarTable_no_external_cross i R h67 h76 cross hc hExt

theorem actual_pair_mem (r : Fin 370) (q : Fin 21) (cross : ThreeHighCross)
    (hq : q ∈ threeHighSecondaryDegreeCodes 6)
    (hc : cross ∈ threeHighCrossDomain (representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)))
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
      threeHighCanonicalRow = true) : (r,q) ∈ remainingPairs := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,hq⟩,?_⟩
  · intro hr
    exact excluded_no_external r hr _ cross hc hExt
  · intro hbad
    obtain ⟨hr,hqfar⟩ := Finset.mem_product.mp hbad
    obtain ⟨h67,h76⟩ := far_R_checked q hqfar
    exact conditional_no_external r hr _ h67 h76 cross hc hExt

end DeficientUOrbitPruning
#print axioms DeficientUOrbitPruning.low_parameters
#print axioms DeficientUOrbitPruning.triangle_parameters
#print axioms DeficientUOrbitPruning.pair_parameters
#print axioms DeficientUOrbitPruning.external_parameters
#print axioms DeficientUOrbitPruning.far_parameters
#print axioms DeficientUOrbitPruning.adjacent_parameters
#print axioms DeficientUOrbitPruning.signed_parameters
#print axioms DeficientUOrbitPruning.far_R_checked
#print axioms DeficientUOrbitPruning.remainingPairs_card
#print axioms DeficientUOrbitPruning.excluded_no_external
#print axioms DeficientUOrbitPruning.conditional_no_external
#print axioms DeficientUOrbitPruning.actual_pair_mem
