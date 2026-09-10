from pathlib import Path
import json,hashlib
p=Path(__file__).parent;survey=p.parent/'full_subset_survey';ns={'__file__':str(survey/'survey.py')};exec((survey/'survey.py').read_text().split('results=[]')[0],ns)
rows=json.loads((survey/'witnesses.json').read_text())['pairs'];manifest=[]
def vec(xs):return '!['+','.join(map(str,xs))+']'
def fs(xs):return '{'+','.join(map(str,xs))+'}' if xs else '∅'
def rectangle(E):
 for x in range(24):
  for y in range(x):
   common=E[x]&E[y]
   if common.bit_count()>1:
    a=(common&-common).bit_length()-1;common&=common-1;b=(common&-common).bit_length()-1;return [x,y,a,b]
for row in rows:
 r,q=row['pair'];a,b,c=row['compact'];U=ns['u'].adjacency(ns['u'].MASKS[a],ns['u'].MASKS[b],ns['perms'][c],None)
 m,x,y,far=row['r_code'];R=[0]*8;edges=[(2*i,2*i+1) for i in range(m+1)]+([(6,x-1)] if x else [])+([(7,y-1)] if y else [])+([(6,7)] if far else [])
 for x,y in edges:R[x]|=1<<y;R[y]|=1<<x
 fixed=U+[x<<15 for x in R]+[0]
 for j in range(6):fixed[23]|=1<<(15+j);fixed[15+j]|=1<<23
 need=[4-R[j].bit_count()-(j<6) for j in range(8)]
 D=[[S for S in ns['candidates'] if len(S)==need[j] and rectangle(ns['add'](fixed,j,S)) is None] for j in range(8)]
 w=row['witness'];S=[i for i in range(15) if w['mask']>>i&1];name=f'SubsetPair{r}_{q}'
 s='import Proofs.Erdos85ThreeHighWitnessedColumnDomains\nimport Proofs.Erdos85ThreeBlockCompactCodes\nimport Proofs.Erdos85ThreeHighSecondaryOrbitTable\nnamespace '+name+'\nopen Erdos85\n'
 s+='def uRows : Fin 15 → BitVec 15 := '+vec(U)+'\ndef rRows : Fin 8 → BitVec 8 := '+vec(R)+'\n'
 s+='def U (i j : Fin 15) : Bool := (uRows i).getLsbD j.val\ndef R (i j : Fin 8) : Bool := (rRows i).getLsbD j.val\n'
 s+='def domains : Fin 8 → List (Finset (Fin 15)) := !['+','.join('['+','.join(map(fs,d))+']' for d in D)+']\n'
 s+='def S : Finset (Fin 15) := '+fs(S)+'\ndef caps : Fin 8 → Nat := '+vec(w['caps'])+'\nend '+name+'\n';(p/(name+'Data.lean')).write_text(s)
 reasons=[]
 for j in range(8):
  rs=[]
  for C in ns['candidates']:
   rs.append('.margin' if len(C)!=need[j] else '.kept' if C in D[j] else '.rectangle '+' '.join(map(str,rectangle(ns['add'](fixed,j,C)))))
  reasons.append(rs)
 s='import '+name+'Data\nnamespace '+name+'\nopen Erdos85\nopen scoped BigOperators\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 50000000\n'
 s+='def reasons : Fin 8 → List ThreeHighColumnDomainReason := !['+','.join('['+','.join(rs)+']' for rs in reasons)+']\n'
 s+='theorem domains_checked : threeHighWitnessedColumnDomainsCheck U R domains reasons = true := by decide\n'
 s+=f'theorem U_eq : U = threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode {a} {b} {c})) := by\n  funext i j\n  revert i j\n  decide\n'
 s+=f'theorem R_eq : R = threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative {q}) := by\n  funext i j\n  revert i j\n  decide\n'
 s+='theorem caps_checked (j : Fin 8) : (domains j).all (fun T => decide ((S ∩ T).card ≤ caps j)) = true := by\n  fin_cases j <;> decide\n'
 s+='theorem deficit : (∑ j : Fin 8, caps j) < ∑ i ∈ S, (4 - encodedRowDegree (U i)) := by decide\nend '+name+'\n'
 for th in ['domains_checked','U_eq','R_eq','caps_checked','deficit']:s+='#print axioms '+name+'.'+th+'\n'
 (p/(name+'Inputs.lean')).write_text(s)
 manifest.append({'name':name,'pair':[r,q],'compact':row['compact'],'witness':w,'files':{n:hashlib.sha256((p/n).read_bytes()).hexdigest() for n in [name+'Data.lean',name+'Inputs.lean']}})
(p/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');print('Generated',len(manifest),'pair inputs; none yet checked')
