"""Independent edge-entry recursion, including4; no producer profile imports."""
from pathlib import Path
from itertools import permutations
import json
import time

P=Path(__file__).parent
S=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n80-m16-quotient')
import hashlib
pins=json.loads((S/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((S/f).read_bytes()).hexdigest()==h
src=json.loads((S/'results.json').read_text())
assert src['status']=='COMPLETE'
began=time.monotonic()
Q=[[0]*5 for _ in range(5)]
sums=[0]*5;squares=[0]*5;left=[4]*5
edges=[(i,j) for i in range(5) for j in range(i+1,5)]
found=set();states=[0]
def feasible(v):
    for a in [0,1,2]:
        rem=9-a-sums[v]
        if not 0<=rem<=4*left[v]:continue
        if left[v]:
            q,r=divmod(rem,left[v]);lower=(left[v]-r)*q*q+r*(q+1)*(q+1)
        else:lower=0
        if a*a+squares[v]+lower<=24:return True
    return False
def visit(t):
    if t==len(edges):
        assert all(sum(r)==9 for r in Q)
        assert all(sum(Q[i][k]*Q[j][k] for k in range(5))<=(24 if i==j else 16) for i in range(5) for j in range(i+1))
        found.add(tuple(tuple(r) for r in Q));return
    i,j=edges[t]
    for x in range(5):
        states[0]+=1
        assert states[0]<=1000000 and time.monotonic()-began<60,'independent verification cap'
        Q[i][j]=Q[j][i]=x
        for v in [i,j]:sums[v]+=x;squares[v]+=x*x;left[v]-=1
        if feasible(i) and feasible(j):
            for v in [i,j]:
                if left[v]==0:Q[v][v]=9-sums[v]
            complete=[v for v in range(5) if left[v]==0]
            if all(sum(Q[u][k]*Q[v][k] for k in range(5))<=16 and not(Q[u][u]==Q[v][v]==1 and Q[u][v]>0) for z,u in enumerate(complete) for v in complete[:z]):
                visit(t+1)
        for v in [i,j]:
            if left[v]==0:Q[v][v]=0
            sums[v]-=x;squares[v]-=x*x;left[v]+=1
        Q[i][j]=Q[j][i]=0
visit(0)
expected=set()
for line in (S/'quotients.jsonl').read_text().splitlines():
 flat=json.loads(line);assert len(flat)==25
 expected.add(tuple(tuple(flat[5*i:5*i+5]) for i in range(5)))
assert found==expected and len(found)==210
classes={}
for q in found:
 key=min(tuple(tuple(q[p[i]][p[j]] for j in range(5)) for i in range(5)) for p in permutations(range(5)))
 classes[key]=classes.get(key,0)+1
assert len(classes)==6 and sorted(classes.values())==[15,15,30,30,60,60]
assert all(sum(q[i][i]==1 for i in range(5))==1 for q in found)
result=dict(status='PASS',states=states[0],labelled_matrices=len(found),class_sizes=sorted(classes.values()),seconds=time.monotonic()-began)
(P/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(result)
