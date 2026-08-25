import Proofs.Erdos85OneHighOddProfileSeparatedRepeat
import Proofs.Erdos85FourPairPartitionGeometry

/-!
# Decode odd-profile owner partition codes

The finite odd-profile classifier records each transversal by a `Fin 3`
partition code.  These lemmas expose the corresponding edge of the three
perfect matchings of the four canonical root pairs, in exactly the form used
by the star-or-triangle coherence theorem.
-/

namespace Erdos85

theorem oneHighOwnerPartitionCode_zero_edge
    (i j : Fin 8) (hij : i ≠ j)
    (hjm : j ≠ oneHighStandardMate i)
    (hcode : (oneHighOwnerPartitionCode i j == 0) = true) :
    finFourEdge (oneHighRootPair i) (oneHighRootPair j) = finFourEdge 0 1 ∨
      finFourEdge (oneHighRootPair i) (oneHighRootPair j) =
        finFourEdge 2 3 := by
  decide +revert

theorem oneHighOwnerPartitionCode_one_edge
    (i j : Fin 8) (hij : i ≠ j)
    (hjm : j ≠ oneHighStandardMate i)
    (hcode : (oneHighOwnerPartitionCode i j == 1) = true) :
    finFourEdge (oneHighRootPair i) (oneHighRootPair j) = finFourEdge 0 2 ∨
      finFourEdge (oneHighRootPair i) (oneHighRootPair j) =
        finFourEdge 1 3 := by
  decide +revert

theorem oneHighOwnerPartitionCode_two_edge
    (i j : Fin 8) (hij : i ≠ j)
    (hjm : j ≠ oneHighStandardMate i)
    (hcode : (oneHighOwnerPartitionCode i j == 2) = true) :
    finFourEdge (oneHighRootPair i) (oneHighRootPair j) = finFourEdge 0 3 ∨
      finFourEdge (oneHighRootPair i) (oneHighRootPair j) =
        finFourEdge 1 2 := by
  decide +revert

end Erdos85

#print axioms Erdos85.oneHighOwnerPartitionCode_zero_edge
#print axioms Erdos85.oneHighOwnerPartitionCode_one_edge
#print axioms Erdos85.oneHighOwnerPartitionCode_two_edge
