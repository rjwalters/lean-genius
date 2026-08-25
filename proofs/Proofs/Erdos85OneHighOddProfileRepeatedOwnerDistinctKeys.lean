import Proofs.Erdos85OneHighOddProfileSeparatedRepeat

/-!
# Distinct keys at a shared owner across different partitions

For a four-mate-pair transversal, the key root-pair edge is complementary to
the owner root-pair edge.  Consequently two witnesses sharing an exact owner
but carrying different partition codes cannot carry the same exact key.  At a
two-edge shared branch this will force the selected internal edges to be the
two different matching edges.
-/

namespace Erdos85

/-- Finite label form of complement uniqueness: separated witnesses with a
shared owner and unequal partition codes have unequal repeated keys. -/
theorem oneHigh_sharedOwner_unequalPartitionCode_keys_ne
    (s t u : Fin 8) (key₁ key₂ : OneHighLabelPair)
    (hst : s ≠ t) (htm : t ≠ oneHighStandardMate s)
    (hsu : s ≠ u) (hum : u ≠ oneHighStandardMate s)
    (hkey₁lt : key₁.1 < key₁.2)
    (hkey₁mate : key₁.2 ≠ oneHighStandardMate key₁.1)
    (hkey₁farS : OneHighKeyFarFromSource key₁ s)
    (hkey₁farT : OneHighKeyFarFromSource key₁ t)
    (hkey₂lt : key₂.1 < key₂.2)
    (hkey₂mate : key₂.2 ≠ oneHighStandardMate key₂.1)
    (hkey₂farS : OneHighKeyFarFromSource key₂ s)
    (hkey₂farU : OneHighKeyFarFromSource key₂ u)
    (hcode : oneHighOwnerPartitionCode s t ≠
      oneHighOwnerPartitionCode s u) :
    key₁ ≠ key₂ := by
  native_decide +revert

end Erdos85

#print axioms Erdos85.oneHigh_sharedOwner_unequalPartitionCode_keys_ne
