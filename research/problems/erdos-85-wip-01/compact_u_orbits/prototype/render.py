from pathlib import Path
from itertools import permutations,combinations
import json
out=Path(__file__).resolve().parent;root=out.parent
D=json.loads((root/'witnesses.json').read_text());perms=list(permutations(range(5)));edges=list(combinations(range(5),2));ei={e:i for i,e in enumerate(edges)}
def relabel(m,p):return sum(1<<ei[tuple(sorted((p[i],p[j])))] for bit,(i,j) in enumerate(edges) if m>>bit&1)
stab=[p for p in perms if relabel(129,p)==129]
reps=[(a,b,tuple(p)) for a,b,p in D['representatives']]
witnesses={(w['source'][0],w['source'][1],tuple(w['source'][2])):w for w in D['witnesses']}
def vec(xs):return '!['+','.join(map(str,xs))+']'
s='import Proofs.Erdos85ThreeBlockCandidateDomains\nnamespace UPrototype\nopen Erdos85\n'
s+='def fw : Fin 120 → Fin 5 → Fin 5 := '+vec([vec(p) for p in perms])+'\n'
s+='def inv : Fin 120 → Fin 5 → Fin 5 := '+vec([vec([p.index(i) for i in range(5)]) for p in perms])+'\n'
s+='set_option maxRecDepth 100000 in\nprivate theorem left (p : Fin 120) (i : Fin 5) : inv p (fw p i) = i := by decide +revert\n'
s+='set_option maxRecDepth 100000 in\nprivate theorem right (p : Fin 120) (i : Fin 5) : fw p (inv p i) = i := by decide +revert\n'
s+='def perm (p : Fin 120) : Equiv.Perm (Fin 5) := ⟨fw p,inv p,left p,right p⟩\n'
s+='def repA : Fin 55 → BitVec 10 := '+vec([a for a,b,p in reps])+'\n'
s+='def repB : Fin 55 → BitVec 10 := '+vec([b for a,b,p in reps])+'\n'
s+='def repP : Fin 55 → Fin 120 := '+vec([perms.index(p) for a,b,p in reps])+'\n'
s+='def sig : Fin 8 → Fin 5 → Fin 5 := '+vec([vec(p) for p in stab])+'\n'
s+='def adj (a b : BitVec 10) (p : Fin 120) (x y : Fin 15) : Bool :=\n  threeBlockMatchingAdj ![129,a,b] (perm p) ((@finProdFinEquiv 3 5).symm x) ((@finProdFinEquiv 3 5).symm y)\n'
s+='def label (s : Fin 8) (sw : Bool) (x : Fin 15) : Fin 15 :=\n  let t := (@finProdFinEquiv 3 5).symm x\n  (@finProdFinEquiv 3 5) ((if sw then Equiv.swap 1 2 t.1 else t.1),sig s t.2)\n'
s+='inductive Cert where\n  | cycle (x y a b : Fin 15)\n  | orbit (r : Fin 55) (s : Fin 8) (sw : Bool)\n'
certs=[]
for p in perms:
 t=(66,66,p)
 if t in witnesses:
  w=witnesses[t];r=(w['representative'][0],w['representative'][1],tuple(w['representative'][2]));certs.append(f'Cert.orbit {reps.index(r)} {stab.index(tuple(w["diagonal_permutation"]))} {str(w["swap_rows_1_2"]).lower()}')
 else:
  rows=[set() for _ in range(15)]
  def add(i,j):rows[i].add(j);rows[j].add(i)
  for k,m in enumerate((129,66,66)):
   for bit,(i,j) in enumerate(edges):
    if m>>bit&1:add(5*k+i,5*k+j)
  for i in range(5):add(i,5+i);add(i,10+i);add(5+i,10+p[i])
  x,y,a,b=next((i,j,*sorted(rows[i]&rows[j])[:2]) for i in range(15) for j in range(i+1,15) if len(rows[i]&rows[j])>=2)
  certs.append(f'Cert.cycle {x} {y} {a} {b}')
s+='def cert : Fin 120 → Cert := '+vec(certs)+'\n'
s+='def check (p : Fin 120) : Prop :=\n  match cert p with\n  | .cycle x y a b => x ≠ y ∧ a ≠ b ∧ adj 66 66 p x a = true ∧ adj 66 66 p x b = true ∧ adj 66 66 p y a = true ∧ adj 66 66 p y b = true\n  | .orbit r s sw => Function.Bijective (label s sw) ∧ ∀ x y, adj 66 66 p x y = adj (repA r) (repB r) (repP r) (label s sw x) (label s sw y)\n'
s+='instance (p : Fin 120) : Decidable (check p) := by unfold check; split <;> infer_instance\n'
s+='set_option maxRecDepth 1000000 in\nset_option maxHeartbeats 50000000 in\ntheorem checked (p : Fin 120) : check p := by decide +revert\nend UPrototype\n#print axioms UPrototype.checked\n'
s += (out/'Decoder.lean.inc').read_text()
(out/'Prototype.lean').write_text(s)
print(json.dumps({'permutations':120,'orbit_entries':sum(c.startswith('Cert.orbit') for c in certs),'cycle_entries':sum(c.startswith('Cert.cycle') for c in certs)}))
