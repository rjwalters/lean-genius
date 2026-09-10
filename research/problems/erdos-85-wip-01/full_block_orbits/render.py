from pathlib import Path
import json
p=Path(__file__).parent;data=json.loads((p/'audit.json').read_text());rs=data['records']
def vec(xs):return '!['+','.join(map(str,xs))+']'
def table(field):return vec(vec(r[field]) for r in rs)
s='''import Full_3_3
import Proofs.Erdos85ThreeHighBlockPermutationTransport
namespace FullUBlockOrbits
open Erdos85
set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000
abbrev representative := FullUShard_3_3.representative
'''
s+='def target : Fin 55 → Fin 55 := '+vec(r['target'] for r in rs)+'\n'
s+='def forward : Fin 55 → Fin 15 → Fin 15 := '+table('permutation')+'\n'
s+='def inverse : Fin 55 → Fin 15 → Fin 15 := '+vec(vec(r['permutation'].index(i) for i in range(15)) for r in rs)+'\n'
s+='def blockForward : Fin 55 → Fin 3 → Fin 3 := '+table('blocks')+'\n'
s+='def blockInverse : Fin 55 → Fin 3 → Fin 3 := '+vec(vec(r['blocks'].index(i) for i in range(3)) for r in rs)+'\n'
s+='''theorem inverse_checked (r : Fin 55) :
    (∀ i, inverse r (forward r i) = i) ∧ (∀ i, forward r (inverse r i) = i) := by
  decide +revert
theorem block_inverse_checked (r : Fin 55) :
    (∀ i, blockInverse r (blockForward r i) = i) ∧
      (∀ i, blockForward r (blockInverse r i) = i) := by
  decide +revert
def label (r : Fin 55) : Equiv.Perm (Fin 15) :=
  ⟨forward r,inverse r,(inverse_checked r).1,(inverse_checked r).2⟩
def blockLabel (r : Fin 55) : Equiv.Perm (Fin 3) :=
  ⟨blockForward r,blockInverse r,(block_inverse_checked r).1,(block_inverse_checked r).2⟩
theorem adjacency_checked (r : Fin 55) : ∀ x y,
    representative r x y = representative (target r) (label r x) (label r y) := by
  decide +revert
theorem rows_checked (r : Fin 55) : ∀ k,
    (threeHighCanonicalRow k).image (threeHighEmptyURelabel (label r)) =
      threeHighCanonicalRow (blockLabel r k) := by
  decide +revert

def targets : Finset (Fin 55) := '''+ '{'+','.join(map(str,data['targets']))+'}'+'''
theorem target_mem (r : Fin 55) : target r ∈ targets := by decide +revert
theorem targets_card : targets.card = 29 := by decide

theorem joint_transport (r : Fin 55) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain (representative r) R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (representative r) R cross)
      threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj (representative r) R cross)) :
    ∃ cross' : ThreeHighCross, cross' ∈ threeHighCrossDomain (representative (target r)) R ∧
      encodedExternalBlockCap (threeHighEmptyAdj (representative (target r)) R cross')
        threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj (representative (target r)) R cross') :=
  threeHighBlockPermutation_joint_transport _ _ R (label r) (blockLabel r)
    (rows_checked r) (adjacency_checked r) cross hc hExt hJoint

end FullUBlockOrbits
'''
for n in ['inverse_checked','block_inverse_checked','adjacency_checked','rows_checked','target_mem','targets_card','joint_transport']:s+='#print axioms FullUBlockOrbits.'+n+'\n'
(p/'Certificate.lean').write_text(s)
