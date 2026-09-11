"""Independent edge-entry recursion, including4; no producer profile imports."""
from pathlib import Path
from itertools import permutations
import json
import time

P=Path(__file__).parent
src=json.loads((P/'results.json').read_text())
assert src['status']=='COMPLETE'
began=time.monotonic()
Q=[[0]*6 for _ in range(6)]
sums=[0]*6;squares=[0]*6;left=[5]*6
edges=[(i,j) for i in range(6) for j in range(i+1,6)]
found=set();states=[0]
def feasible(v):
    for a in [0,2]:
        rem=9-a-sums[v]
        if not 0<=rem<=4*left[v]:continue
        if left[v]:
            q,r=divmod(rem,left[v]);lower=(left[v]-r)*q*q+r*(q+1)*(q+1)
        else:lower=0
        if a*a+squares[v]+lower<=21:return True
    return False
def visit(t):
    if t==len(edges):
        assert all(sum(r)==9 for r in Q)
        assert all(sum(Q[i][k]*Q[j][k] for k in range(6))<=(21 if i==j else 13) for i in range(6) for j in range(i+1))
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
            complete=[v for v in range(6) if left[v]==0]
            if all(sum(Q[u][k]*Q[v][k] for k in range(6))<=13 for z,u in enumerate(complete) for v in complete[:z]):
                visit(t+1)
        for v in [i,j]:
            if left[v]==0:Q[v][v]=0
            sums[v]-=x;squares[v]-=x*x;left[v]+=1
        Q[i][j]=Q[j][i]=0
visit(0)
expected=set();orbits=[]
for q in src['matrices']:
    orbit={tuple(tuple(q[p[i]][p[j]] for j in range(6)) for i in range(6)) for p in permutations(range(6))}
    expected|=orbit;orbits.append(orbit)
assert found==expected
classes={min(o):len(o) for o in orbits}
assert len(found)==70 and sorted(classes.values())==[10,60]
result=dict(status='PASS',states=states[0],labelled_matrices=len(found),
            source_matrices=len(src['matrices']),class_sizes=sorted(classes.values()),
            seconds=time.monotonic()-began,
            representatives=[list(map(list,q)) for q in sorted(classes)])
(P/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(result)
