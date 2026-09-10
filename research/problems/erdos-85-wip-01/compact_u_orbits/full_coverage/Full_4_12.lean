import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeBlockOrbitCertificate
namespace FullUShard_4_12
open Erdos85
set_option maxRecDepth 1000000
def adj (a b : Fin 15) (p : Fin 120) (x y : Fin 15) : Bool :=
  threeBlockFullParameterAdj (threeBlockFirstRowEmbed (threeBlockCompactCode a b p))
    ((@finProdFinEquiv 3 5).symm x) ((@finProdFinEquiv 3 5).symm y)
def repA : Fin 55 → Fin 15 := ![6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9]
def repB : Fin 55 → Fin 15 := ![6,6,6,9,9,9,9,9,9,9,9,3,3,10,10,10,10,10,9,9,9,9,9,9,9,9,9,9,10,10,10,10,10,10,4,4,4,7,7,7,8,8,8,8,8,13,13,13,13,13,12,12,12,12,12]
def repP : Fin 55 → Fin 120 := ![14,15,16,5,14,16,20,21,54,55,61,0,1,0,5,21,54,55,5,15,16,21,54,55,58,60,82,94,1,21,54,55,58,79,0,1,14,0,14,16,0,14,15,55,66,0,1,55,67,80,5,14,60,82,90]
def representative (r : Fin 55) := adj (repA r) (repB r) (repP r)
def cert : Fin 120 → ThreeBlockOrbitCertificate 55 := ![.orbit 45 86 true,.cycle 3 14 8 13,.cycle 2 8 3 12,.cycle 2 13 3 7,.cycle 2 8 3 12,.cycle 6 12 9 11,.cycle 1 12 6 11,.cycle 1 12 6 11,.cycle 1 12 6 11,.cycle 1 9 6 11,.cycle 1 12 6 11,.cycle 1 9 6 11,.cycle 2 8 3 12,.cycle 2 11 7 12,.cycle 6 14 9 13,.cycle 1 9 6 11,.orbit 48 86 true,.cycle 1 9 6 11,.cycle 2 8 3 12,.cycle 2 11 7 12,.cycle 4 6 9 14,.cycle 1 9 6 11,.cycle 2 13 3 7,.cycle 1 9 6 11,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 0 11 1 5,.cycle 0 11 1 5,.cycle 0 11 1 5,.cycle 0 11 1 5,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 0 11 1 5,.cycle 0 11 1 5,.cycle 0 11 1 5,.cycle 0 11 1 5,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 0 11 1 5,.cycle 0 11 1 5,.cycle 0 11 1 5,.cycle 0 11 1 5,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 2 5 7 12,.cycle 2 5 7 12,.cycle 2 5 7 12,.cycle 2 5 7 12,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 2 5 7 12,.cycle 2 5 7 12,.cycle 1 9 6 11,.cycle 2 5 7 12,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 2 5 7 12,.cycle 2 5 7 12,.cycle 1 9 6 11,.cycle 2 5 7 12,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 7 5 10,.cycle 0 7 5 10,.orbit 49 86 true,.cycle 3 14 8 13,.cycle 5 14 7 13,.cycle 2 8 3 12,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 1 12 6 11,.cycle 1 12 6 11,.cycle 1 9 6 11,.cycle 1 12 6 11,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 2 11 7 12,.cycle 2 8 3 12,.cycle 1 9 6 11,.cycle 4 6 9 14,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 6 1 10,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 4 13 9 14,.orbit 46 86 true,.cycle 2 13 3 7,.cycle 2 8 3 12,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 1 12 6 11,.cycle 1 12 6 11,.cycle 1 9 6 11,.cycle 1 12 6 11,.cycle 0 7 5 10,.cycle 0 7 5 10,.cycle 2 11 7 12,.cycle 2 8 3 12,.cycle 1 9 6 11,.orbit 47 86 true]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 50000000 in
theorem checked (p : Fin 120) : (cert p).Valid (adj 4 12 p) representative := by
  decide +revert
theorem covered (p : Fin 120) (hfree : encodedC4Free (adj 4 12 p) = true) :
    ∃ (r : Fin 55) (q : Fin 120) (sw : Bool), ∀ x y,
      adj 4 12 p x y = representative r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y) :=
  (cert p).covered (adj 4 12 p) representative (checked p) hfree
end FullUShard_4_12
#print axioms FullUShard_4_12.checked
#print axioms FullUShard_4_12.covered
