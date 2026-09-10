"""Render independently kernel-checkable U orbit shards from audited witnesses."""
from pathlib import Path
from itertools import permutations, combinations
import argparse
import hashlib
import json

parser = argparse.ArgumentParser()
parser.add_argument('--witnesses', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--a', type=int, required=True, choices=range(15))
parser.add_argument('--b', type=int, required=True, choices=range(15))
parser.add_argument('--missing', type=int, choices=range(5))
args = parser.parse_args()
data = json.loads(args.witnesses.read_text())
perms = list(permutations(range(5)))
edges = list(combinations(range(5), 2))
masks = [129,257,513,34,66,514,20,68,260,24,40,136,528,288,192]
def key(t): return (t[0],t[1],tuple(t[2]),*t[3:])
reps = [key(t) for t in data['representatives']]
witnesses = {key(w['source']):w for w in data['witnesses']}
deficient = args.missing is not None
assert all(len(r)==(4 if deficient else 3) for r in reps)
n = len(reps)
def vec(xs): return '!['+','.join(map(str,xs))+']'
tag = f'{args.a}_{args.b}' + (f'_{args.missing}' if deficient else '')
ns = ('Deficient' if deficient else 'Full') + 'UShard_' + tag
code = 'threeBlockDeficientCompactCode' if deficient else 'threeBlockCompactCode'
embed = 'threeBlockDeficientFirstRowEmbed' if deficient else 'threeBlockFirstRowEmbed'
adj = 'threeBlockDeficientParameterAdj' if deficient else 'threeBlockFullParameterAdj'
extra_arg = ' (d : Fin 5)' if deficient else ''
extra_value = ' d' if deficient else ''
s = f'''import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeBlockOrbitCertificate
namespace {ns}
open Erdos85
set_option maxRecDepth 1000000
def adj (a b : Fin 15) (p : Fin 120){extra_arg} (x y : Fin 15) : Bool :=
  {adj} ({embed} ({code} a b p{extra_value}))
    ((@finProdFinEquiv 3 5).symm x) ((@finProdFinEquiv 3 5).symm y)
'''
s += f'def repA : Fin {n} → Fin 15 := '+vec([masks.index(r[0]) for r in reps])+'\n'
s += f'def repB : Fin {n} → Fin 15 := '+vec([masks.index(r[1]) for r in reps])+'\n'
s += f'def repP : Fin {n} → Fin 120 := '+vec([perms.index(r[2]) for r in reps])+'\n'
if deficient: s += f'def repD : Fin {n} → Fin 5 := '+vec([r[3] for r in reps])+'\n'
s += f'def representative (r : Fin {n}) := adj (repA r) (repB r) (repP r)'+(' (repD r)' if deficient else '')+'\n'
certs=[]
for p in perms:
    t=(masks[args.a],masks[args.b],p)+((args.missing,) if deficient else ())
    if t in witnesses:
        w=witnesses[t]
        certs.append(f'.orbit {reps.index(key(w["representative"]))} {perms.index(tuple(w["diagonal_permutation"]))} {str(w["swap_rows_1_2"]).lower()}')
    else:
        rows=[set() for _ in range(15)]
        def add(i,j): rows[i].add(j);rows[j].add(i)
        for k,m in enumerate((129,*t[:2])):
            for bit,(i,j) in enumerate(edges):
                if m>>bit&1: add(5*k+i,5*k+j)
        for i in range(5):
            add(i,5+i);add(i,10+i)
            if not deficient or i!=args.missing: add(5+i,10+p[i])
        x,y,a,b=next((i,j,*sorted(rows[i]&rows[j])[:2]) for i in range(15) for j in range(i+1,15) if len(rows[i]&rows[j])>=2)
        certs.append(f'.cycle {x} {y} {a} {b}')
s += f'def cert : Fin 120 → ThreeBlockOrbitCertificate {n} := '+vec(certs)+'\n'
target=f'adj {args.a} {args.b} p'+(f' {args.missing}' if deficient else '')
s += f'''set_option maxRecDepth 1000000 in
set_option maxHeartbeats 50000000 in
theorem checked (p : Fin 120) : (cert p).Valid ({target}) representative := by
  decide +revert
theorem covered (p : Fin 120) (hfree : encodedC4Free ({target}) = true) :
    ∃ (r : Fin {n}) (q : Fin 120) (sw : Bool), ∀ x y,
      {target} x y = representative r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y) :=
  (cert p).covered ({target}) representative (checked p) hfree
end {ns}
#print axioms {ns}.checked
#print axioms {ns}.covered
'''
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(s)
receipt={'namespace':ns,'a':args.a,'b':args.b,'missing':args.missing,
         'representatives':n,'permutations':120,'cycle_entries':sum(c.startswith('.cycle') for c in certs),
         'orbit_entries':sum(c.startswith('.orbit') for c in certs),
         'source_sha256':hashlib.sha256(s.encode()).hexdigest(),
         'witness_sha256':hashlib.sha256(args.witnesses.read_bytes()).hexdigest()}
args.output.with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
