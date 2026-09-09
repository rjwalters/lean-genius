from pathlib import Path
from contextlib import redirect_stdout
from io import StringIO
from collections import Counter
import json,runpy

seed_path=Path(__file__).resolve().parent.parent/'baer-repair-gate'/'check.py'
with redirect_stdout(StringIO()):
    z=runpy.run_path(str(seed_path))
q,r=z['q'],z['p']
V,S,P,idx,adj,absolute=z['V'],z['S'],z['P'],z['idx'],z['adj'],z['absolute']
owners={v:next(iter(adj[v]&S)) for v in V}
cases=[]
for coordinates in [[(1,0,0),(1,0,1)],[(1,0,0),(0,1,0)]]:
    T={idx[v] for v in coordinates}
    assert T<=S and len(T)==r-3
    vertices=V|T
    A={v:adj[v]&vertices for v in vertices}
    Uext={v for v in V if owners[v] in T}
    U=T|Uext
    s=len(T); a=len(Uext&absolute)
    e=sum(len(adj[v]&T) for v in T)//2
    assert len(vertices)==q*q-3 and len(Uext)==s*(q-r)
    assert all(len(A[v])==q-int(v in absolute)+int(owners[v] in T) for v in V)
    assert all(len(A[v])==q-r+len(adj[v]&T) for v in T)
    deficit=sum(q-len(A[v]) for v in vertices)
    assert deficit==(6-r)*q-7*r-2*e
    outside_deficient={v for v in V-U if len(A[v])==q-1}
    assert len(outside_deficient)==q-r-a and len(outside_deficient)>=r*r-3*r+6
    assert a<=2*s
    cases.append({'retained_coordinates':coordinates,'vertices':len(vertices),
                  'e_T':e,'a':a,'degree_histogram':dict(sorted(Counter(map(len,A.values())).items())),
                  'induced_support_size':len(U),'outside_deficient':len(outside_deficient),
                  'total_degree_deficit':deficit,'required_net_edge_deletions':-deficit//2})
out={'PASS':True,'scope':'deterministic degree and induced-support gate only','cases':cases}
Path(__file__).with_name('verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
