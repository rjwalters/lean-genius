"""Uniform root-orbit arithmetic repair of the saved local-state witness."""
from pathlib import Path
from itertools import combinations, permutations
import json, hashlib
import sympy as sp

ROOT=Path(__file__).parent
q=sp.Symbol('q',integer=True,positive=True)
error=sp.Symbol('error');c=sp.Symbol('c');z=sp.Symbol('z')
parse=lambda x:sp.sympify(x,locals={'q':q,'error':error})
records=json.loads((ROOT/'uniform-local-certificate.json').read_text())
kernel=sp.Matrix([-1,1,1,-1,1,-1,-1,1,0])
edges=list(combinations(range(3),2))

def moved(state,perm):
    out=[0]*8
    for bits,value in enumerate(state):
        image=sum(1<<perm[i] for i in range(3) if bits&(1<<i))
        out[image]=value
    return tuple(out)

def positive(expr,Q):
    num,den=sp.fraction(sp.cancel(expr))
    np=sp.Poly(sp.expand(num.subs(q,Q+z)),z)
    dp=sp.Poly(sp.expand(den.subs(q,Q+z)),z)
    assert all(x>=0 for x in np.all_coeffs())
    assert all(x>=0 for x in dp.all_coeffs()) and dp.eval(0)>0

# From k=4, powers of two modulo720 have period12, preserving parity.
assert pow(2,16,720)==pow(2,4,720)
residues={d:sorted({pow(2,k,720) for k in range(4,16)
                   if (4 if k%2==0 else 2)==d}) for d in (2,4)}
results=[]
for record in records:
    d=record['d'];Q=record['q_min'];center=parse(record['C5_center'])
    empty=record['distributions']['0']
    S=[sp.Matrix([parse(x) for x in state]) for state in empty['states']]
    assert len(S)==9
    assert all(sp.expand(x)==0 for x in
               sum((k*v*v.T for k,v in zip(kernel,S)),sp.zeros(8)))
    empty['weights']=[str(sp.expand(parse(w)+2*k))
                      for w,k in zip(empty['weights'],kernel)]
    state_count=0
    for sigma,item in record['distributions'].items():
        sigma=int(sigma)
        adj={edge:(sigma>>i)&1 for i,edge in enumerate(edges)}
        group=[perm for perm in permutations(range(3))
               if all(adj[edge]==adj[tuple(sorted((perm[edge[0]],perm[edge[1]])))]
                      for edge in edges)]
        states=[tuple(map(parse,state)) for state in item['states']]
        weights=list(map(parse,item['weights']))
        lookup=dict(zip(states,weights));assert len(lookup)==len(states)
        for state,w in zip(states,weights):
            h=sum(moved(state,perm)==state for perm in group)
            for perm in group:assert sp.cancel(lookup[moved(state,perm)]-w)==0
            for e in [-sp.Rational(1,2),sp.Rational(1,2)]:
                positive(w.subs(error,e),Q)
            # Counts divided by stabilizer are integer for every integer C5.
            quot=sp.cancel(w.subs(error,c-center)/h)
            assert sp.diff(quot,c).is_Integer
            num,den=sp.fraction(sp.factor(quot.subs(c,0)))
            assert den.is_Integer and 720%den==0
            assert sp.Poly(num,q).domain==sp.ZZ
            assert all(num.subs(q,a)%den==0 for a in residues[d])
            state_count+=1
    results.append({'d':d,'q_min':Q,'state_count':state_count,
                    'residues_mod720':residues[d],
                    'moment_preserving_shift':True,'nonnegative':'PASS',
                    'orbit_invariance':'PASS','stabilizer_divisibility':'PASS'})
(ROOT/'orbit-repaired-certificate.json').write_text(json.dumps(records,indent=2)+'\n')
(ROOT/'orbit-repair-check.json').write_text(json.dumps({
    'results':results,'shift':[int(2*x) for x in kernel],
    'source_sha256':hashlib.sha256((ROOT/'uniform-local-certificate.json').read_bytes()).hexdigest(),
    'scope':'Repairs root-permutation arithmetic only; no coherent graph assembly.'},indent=2)+'\n')
print(json.dumps(results,indent=2))
