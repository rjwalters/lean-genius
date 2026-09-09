"""Necessary root-permutation conditions on the supplied state multiplicities."""
from pathlib import Path
from itertools import combinations,permutations
import json
import sympy as sp

p=Path(__file__).parent
q=sp.Symbol('q',integer=True,positive=True)
error=sp.Symbol('error')
parse=lambda x:sp.sympify(x,locals={'q':q,'error':error})
records=json.loads((p/'uniform-local-certificate.json').read_text())
edges=list(combinations(range(3),2))
def moved(state,perm):
    out=[0]*8
    for bits,value in enumerate(state):
        image=sum(1<<perm[i] for i in range(3) if bits&(1<<i))
        out[image]=value
    return tuple(out)

results=[]
for k in range(4,13):
    Q=2**k;record=next(r for r in records if r['d']==(4 if k%2==0 else 2))
    center=parse(record['C5_center']).subs(q,Q)
    c=sp.floor(center+sp.Rational(1,2));sub={q:Q,error:c-center}
    failures=[]
    for sigma,item in record['distributions'].items():
        sigma=int(sigma)
        adj={e:(sigma>>i)&1 for i,e in enumerate(edges)}
        group=[perm for perm in permutations(range(3))
               if all(adj[e]==adj[tuple(sorted((perm[e[0]],perm[e[1]])))] for e in edges)]
        states=[tuple(parse(x).subs(sub) for x in state) for state in item['states']]
        weights=[parse(x).subs(sub) for x in item['weights']]
        assert len(set(states))==len(states)
        lookup=dict(zip(states,weights))
        for i,(state,w) in enumerate(zip(states,weights)):
            assert w.is_Integer
            stabilizer=sum(moved(state,perm)==state for perm in group)
            if w%stabilizer:
                failures.append({'sigma':sigma,'state':i,'type':'stabilizer divisibility',
                                 'weight':str(w),'divisor':stabilizer})
            for perm in group:
                other=moved(state,perm)
                if lookup.get(other,0)!=w:
                    failures.append({'sigma':sigma,'state':i,'type':'orbit invariance'})
                    break
    results.append({'k':k,'q':Q,'C5':str(c),'failures':failures})
(p/'root-orbit-check.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
