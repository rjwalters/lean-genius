import SubsetPair20_3Exclusion
import SubsetPair20_14Exclusion
import SubsetPair20_15Exclusion
import SubsetPair20_16Exclusion
import SubsetPair26_3Exclusion
import SubsetPair26_6Exclusion
import SubsetPair26_8Exclusion
import SubsetPair26_12Exclusion
import SubsetPair26_14Exclusion
import SubsetPair26_15Exclusion
import SubsetPair26_16Exclusion
import SubsetPair26_17Exclusion
import SubsetPair26_18Exclusion
namespace SubsetCapacityBatch
open Erdos85
attribute [local irreducible] threeHighCrossDomain
def pair : Fin 13 → Fin 55 × Fin 21 := ![(20,3),(20,14),(20,15),(20,16),(26,3),(26,6),(26,8),(26,12),(26,14),(26,15),(26,16),(26,17),(26,18)]
def U : Fin 13 → (Fin 15 → Fin 15 → Bool) := ![threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)),threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82))]
def R : Fin 13 → (Fin 8 → Fin 8 → Bool) := ![threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 15),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 16),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 6),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 8),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 12),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 15),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 16),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 17),threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 18)]
def pairs : Finset (Fin 55 × Fin 21) := Finset.univ.image pair
theorem pairs_card : pairs.card = 13 := by decide
theorem impossible (i : Fin 13) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (U i) (R i))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (U i) (R i) cross) threeHighCanonicalRow = true) : False := by
  fin_cases i
  · exact SubsetPair20_3.impossible cross hc he
  · exact SubsetPair20_14.impossible cross hc he
  · exact SubsetPair20_15.impossible cross hc he
  · exact SubsetPair20_16.impossible cross hc he
  · exact SubsetPair26_3.impossible cross hc he
  · exact SubsetPair26_6.impossible cross hc he
  · exact SubsetPair26_8.impossible cross hc he
  · exact SubsetPair26_12.impossible cross hc he
  · exact SubsetPair26_14.impossible cross hc he
  · exact SubsetPair26_15.impossible cross hc he
  · exact SubsetPair26_16.impossible cross hc he
  · exact SubsetPair26_17.impossible cross hc he
  · exact SubsetPair26_18.impossible cross hc he
theorem no_joint (i : Fin 13) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (U i) (R i))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (U i) (R i) cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj (U i) (R i) cross) := (impossible i cross hc he).elim
end SubsetCapacityBatch
#print axioms SubsetCapacityBatch.pairs_card
#print axioms SubsetCapacityBatch.impossible
#print axioms SubsetCapacityBatch.no_joint
