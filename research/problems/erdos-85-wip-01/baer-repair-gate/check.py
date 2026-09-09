"""Deterministic PG(2,25) seed and exact repair-obstruction checks; no search."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib,json

p=5
q=p*p
# F25=F5[u]/(u^2-2), encoded a+5b.
def add(x,y): return ((x%p+y%p)%p)+p*((x//p+y//p)%p)
def mul(x,y):
    a,b=x%p,x//p
    c,d=y%p,y//p
    return ((a*c+2*b*d)%p)+p*((a*d+b*c)%p)
def dot(v,w):
    z=0
    for a,b in zip(v,w): z=add(z,mul(a,b))
    return z
# Explicit Frobenius a+bu -> a-bu, avoiding integer-negation precedence.
def frob(v): return tuple(x%p+p*((-(x//p))%p) for x in v)
P=[(1,a,b) for a in range(q) for b in range(q)]+[(0,1,a) for a in range(q)]+[(0,0,1)]
idx={v:i for i,v in enumerate(P)}
S={i for i,v in enumerate(P) if all(x<p for x in v)}
absolute={i for i,v in enumerate(P) if dot(v,v)==0}
assert len(P)==q*q+q+1 and len(S)==q+p+1 and len(absolute)==q+1
adj=[{j for j,w in enumerate(P) if i!=j and dot(v,w)==0} for i,v in enumerate(P)]
V=set(range(len(P)))-S
H={i:adj[i]&V for i in V}
T=absolute&V
assert len(V)==q*q-p and len(T)==q-p
assert all(len(adj[i]&S)==1 for i in V)
assert all(len(H[i])==q-(i in T) for i in V)
assert all(len(H[i]&T)<=2 for i in V)
assert all(not (H[i]&T) for i in T)
bits={i:sum(1<<j for j in H[i]) for i in V}
assert all((bits[i]&bits[j]).bit_count()<=1 for i,j in combinations(sorted(V),2))
def edge(x,y): return tuple(sorted((x,y)))
def paths(a,b):
    return [(a,x,y,b) for x in sorted(H[a]) for y in sorted(H[b]) if y in H[x]]
hist=Counter()
for a,b in combinations(sorted(T),2):
    assert b not in H[a]
    ps=paths(a,b)
    used=set()
    for w in ps:
        es={edge(w[j],w[j+1]) for j in range(3)}
        assert len(es)==3 and not used&es
        used |= es
    assert len(ps)>=q-3
    hist[len(ps)]+=1
matching={edge(a,idx[frob(P[a])]) for a in T}
assert len(matching)==len(T)//2
assert {a for e in matching for a in e}==T and all(a!=b for a,b in matching)
loads=Counter()
matching_paths=0
for a,b in sorted(matching):
    ps=paths(a,b)
    matching_paths+=len(ps)
    for w in ps:
        loads.update(edge(w[j],w[j+1]) for j in range(3))
assert max(loads.values())<=2
data={'q':q,'subfield_order':p,'vertices':len(V),'deficits':len(T),
      'degree_histogram':dict(sorted(Counter(len(H[i]) for i in V).items())),
      'deficit_pair_length3_histogram':dict(sorted(hist.items())),
      'conjugate_matching_edges':len(matching),'conjugate_matching_paths':matching_paths,
      'max_deletion_path_load':max(loads.values()),
      'universal_matching_deletion_lower_bound':(q-p)*(q-3)//4,
      'conjugate_matching_deletion_lower_bound':(matching_paths+1)//2,
      'adjacency_sha256':hashlib.sha256(json.dumps([(i,sorted(H[i])) for i in sorted(V)]).encode()).hexdigest(),
      'PASS':True,'scope':'deterministic seed and necessary deletion bounds; no repaired graph'}
Path(__file__).with_name('verification.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data,indent=2))
