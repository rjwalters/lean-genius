"""Check exact two-colored row-degree marginals of the supplied state census."""
from pathlib import Path
from itertools import combinations,permutations
import json
import sympy as sp

ROOT=Path(__file__).parent
q=sp.Symbol('q',integer=True,positive=True);error=sp.Symbol('error')
parse=lambda x:sp.sympify(x,locals={'q':q,'error':error})
edges=list(combinations(range(3),2));results=[]
for record in json.loads((ROOT/'orbit-repaired-certificate.json').read_text()):
    d=record['d'];n=q*q
    # Type index is A + 2D, allowing A/D overlap on triangle-free edges.
    degree=[n-2*q+d,q-d,q-1-d,d]
    counts=sp.zeros(4)
    for sigma,item in record['distributions'].items():
        sigma=int(sigma);A={e:(sigma>>i)&1 for i,e in enumerate(edges)}
        perms=list(permutations(range(3)))
        aut=sum(all(A[e]==A[tuple(sorted((p[e[0]],p[e[1]])))] for e in edges) for p in perms)
        for state,w in zip(item['states'],item['weights']):
            state=list(map(parse,state));w=parse(w);types={}
            for a,b in edges:
                k=next(x for x in range(3) if x not in (a,b))
                common=state[(1<<a)|(1<<b)]+state[7]+A[tuple(sorted((a,k)))]*A[tuple(sorted((b,k)))]
                assert common in (0,1)
                types[a,b]=A[a,b]+2*(1-common)
            for p in perms:
                u=types[tuple(sorted((p[0],p[1])))];v=types[tuple(sorted((p[0],p[2])))]
                counts[u,v]+=w/aut
    failures=[]
    for u in range(4):
        for v in range(4):
            expected=n*degree[u]*(degree[v]-int(u==v))
            residual=sp.factor(counts[u,v]-expected)
            if residual!=0:failures.append({'u':u,'v':v,'residual':str(residual)})
    results.append({'d':d,'failures':failures,'status':'PASS' if not failures else 'FAIL'})
(ROOT/'joint-pair-degrees.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
