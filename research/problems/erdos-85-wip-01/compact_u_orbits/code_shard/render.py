from pathlib import Path
from itertools import permutations, combinations
import json
import argparse

out = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--witnesses', type=Path, default=out.parent / 'witnesses.json')
args = parser.parse_args()
data = json.loads(args.witnesses.read_text())
perms = list(permutations(range(5)))
edges = list(combinations(range(5), 2))
masks = [129,257,513,34,66,514,20,68,260,24,40,136,528,288,192]
reps = [(a,b,tuple(p)) for a,b,p in data['representatives']]
witnesses = {(w['source'][0],w['source'][1],tuple(w['source'][2])):w for w in data['witnesses']}
def vec(xs): return '![' + ','.join(map(str,xs)) + ']'

s = '''import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeBlockOrbitCertificate
namespace UCodeShard
open Erdos85
def adj (a b : Fin 15) (p : Fin 120) (x y : Fin 15) : Bool :=
  threeBlockFullParameterAdj (threeBlockFirstRowEmbed (threeBlockCompactCode a b p))
    ((@finProdFinEquiv 3 5).symm x) ((@finProdFinEquiv 3 5).symm y)
'''
s += 'def repA : Fin 55 → Fin 15 := ' + vec([masks.index(a) for a,b,p in reps]) + '\n'
s += 'def repB : Fin 55 → Fin 15 := ' + vec([masks.index(b) for a,b,p in reps]) + '\n'
s += 'def repP : Fin 55 → Fin 120 := ' + vec([perms.index(p) for a,b,p in reps]) + '\n'
s += 'def representative (r : Fin 55) := adj (repA r) (repB r) (repP r)\n'
certs = []
for p in perms:
    t = (66,66,p)
    if t in witnesses:
        w = witnesses[t]
        r = (w['representative'][0],w['representative'][1],tuple(w['representative'][2]))
        certs.append(f'.orbit {reps.index(r)} {perms.index(tuple(w["diagonal_permutation"]))} {str(w["swap_rows_1_2"]).lower()}')
    else:
        rows = [set() for _ in range(15)]
        def add(i,j): rows[i].add(j); rows[j].add(i)
        for k,m in enumerate((129,66,66)):
            for bit,(i,j) in enumerate(edges):
                if m>>bit&1: add(5*k+i,5*k+j)
        for i in range(5): add(i,5+i); add(i,10+i); add(5+i,10+p[i])
        x,y,a,b = next((i,j,*sorted(rows[i]&rows[j])[:2]) for i in range(15) for j in range(i+1,15) if len(rows[i]&rows[j])>=2)
        certs.append(f'.cycle {x} {y} {a} {b}')
s += 'def cert : Fin 120 → ThreeBlockOrbitCertificate 55 := ' + vec(certs) + '\n'
s += '''set_option maxRecDepth 1000000 in
set_option maxHeartbeats 50000000 in
theorem checked (p : Fin 120) : (cert p).Valid (adj 4 4 p) representative := by
  decide +revert

theorem covered (p : Fin 120) (hfree : encodedC4Free (adj 4 4 p) = true) :
    ∃ (r : Fin 55) (q : Fin 120) (sw : Bool), ∀ x y,
      adj 4 4 p x y = representative r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y) :=
  (cert p).covered (adj 4 4 p) representative (checked p) hfree

def arbitraryAdj (π : Equiv.Perm (Fin 5)) (x y : Fin 15) : Bool :=
  threeBlockFullParameterAdj
    (threeBlockFirstRowEmbed (![finFiveMatchingMaskCode 4,finFiveMatchingMaskCode 4],π))
    ((@finProdFinEquiv 3 5).symm x) ((@finProdFinEquiv 3 5).symm y)

theorem arbitrary_covered (π : Equiv.Perm (Fin 5))
    (hfree : encodedC4Free (arbitraryAdj π) = true) :
    ∃ (r : Fin 55) (q : Fin 120) (sw : Bool), ∀ x y,
      arbitraryAdj π x y = representative r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y) := by
  obtain ⟨p,rfl⟩ := finFivePermutationCode_surjective π
  exact covered p hfree
end UCodeShard
#print axioms UCodeShard.checked
#print axioms UCodeShard.covered
#print axioms UCodeShard.arbitrary_covered
'''
(out / 'Shard.lean').write_text(s)
print(json.dumps({'permutations':120,'orbit_entries':sum(c.startswith('.orbit') for c in certs),'cycle_entries':sum(c.startswith('.cycle') for c in certs)}))
