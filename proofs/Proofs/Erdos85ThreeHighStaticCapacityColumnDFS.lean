import Proofs.Erdos85ThreeHighCapacityColumnDFS
import Proofs.Erdos85ThreeHighStaticColumnPruning

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

def threeHighStaticCapacityColumnDFS : ThreeHighExternalSearch := fun U R accept =>
  threeHighCapacityColumnDFSWith U R (threeHighStaticPrunedColumnList U R) accept

theorem threeHighStaticCapacityColumnDFS_sound :
    ThreeHighExternalSearchSound threeHighStaticCapacityColumnDFS := by
  intro U R accept cross hc hExt ha
  apply threeHighCapacityColumnDFSWith_witness U R _ accept cross hc hExt _ ha
  have hcap := hExt
  rw [threeHighExternalBlockCap_factor] at hcap
  simp only [Bool.and_eq_true] at hcap
  intro j
  exact threeHighStaticPrunedColumnList_complete U R cross hc hcap.2 j

end Erdos85
#print axioms Erdos85.threeHighStaticCapacityColumnDFS_sound
