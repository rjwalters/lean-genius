from pathlib import Path
p=Path(__file__).parent;ns={'__file__':str(p/'generate_tree.py')};exec((p/'generate_tree.py').read_text().split('start=time.monotonic();counts=')[0],ns)
def vec(xs):return '!['+','.join(map(str,xs))+']'
def fs(S):return '{'+','.join(map(str,S))+'}' if S else '∅'
s='''import Proofs.Erdos85ThreeHighWitnessedColumnCover
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
namespace Zero26
open Erdos85
set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000
'''
s+='def uRows : Fin 15 → BitVec 15 := '+vec(ns['U'])+'\ndef rRows : Fin 8 → BitVec 8 := '+vec(ns['R'])+'\n'
s+='def U (i j : Fin 15) : Bool := (uRows i).getLsbD j.val\ndef R (i j : Fin 8) : Bool := (rRows i).getLsbD j.val\n'
s+='def domains : Fin 8 → List (Finset (Fin 15)) := !['+','.join('['+','.join(map(fs,D))+']' for D in ns['domains'])+']\n'
s+='def table : Fin 0 → ThreeHighCross := Fin.elim0\nend Zero26\n';(p/'Zero26Data.lean').write_text(s)
rows=[]
for j in range(8):
 rs=[]
 for S in ns['candidates']:
  if len(S)!=ns['needR'][j]:r='.margin'
  elif S in ns['domains'][j]:r='.kept'
  else:r='.rectangle '+' '.join(map(str,ns['rectangle'](ns['add'](ns['fixed'],j,S))))
  rs.append(r)
 rows.append(rs)
s='''import Zero26Data
namespace Zero26
open Erdos85
set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000
'''
s+='def reasons : Fin 8 → List ThreeHighColumnDomainReason := !['+','.join('['+','.join(rs)+']' for rs in rows)+']\n'
s+='''theorem domains_checked : threeHighWitnessedColumnDomainsCheck U R domains reasons = true := by decide
theorem U_eq : U = threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)) := by
  funext i j
  revert i j
  decide
theorem R_eq : R = threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14) := by
  funext i j
  revert i j
  decide
theorem swaps_valid : threeHighRSwapPairsValid R [(2,3),(4,5),(6,7)] = true := by decide
theorem table_no_joint (i : Fin 0) : ¬ ThreeHighJointWitness (threeHighEmptyAdj U R (table i)) := Fin.elim0 i
end Zero26
#print axioms Zero26.domains_checked
#print axioms Zero26.U_eq
#print axioms Zero26.R_eq
#print axioms Zero26.swaps_valid
#print axioms Zero26.table_no_joint
'''
(p/'Zero26Inputs.lean').write_text(s)
