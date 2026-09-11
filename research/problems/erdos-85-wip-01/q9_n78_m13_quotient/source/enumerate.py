"""Finite necessary quotient cover only; original100k states/root,60s total."""
from itertools import product
from collections import defaultdict
from pathlib import Path
import json
import time

P=Path(__file__).parent
assert not (P/'results.json').exists(), 'do not overwrite or retry a capped cover'
profiles=[(a,x) for a in [0,2] for x in product(range(4),repeat=5)
          if a+sum(x)==9 and a*a+sum(v*v for v in x)<=21]
roots=[(a,x) for a,x in profiles if list(x)==sorted(x)]
assert len(profiles)==190 and len(roots)==9
by_prefix=[]
for i in range(6):
    index=defaultdict(list)
    for a,x in profiles:index[x[:i]].append((a,x))
    by_prefix.append(index)
began=time.monotonic()
cases=[]
all_matrices=[]

class Capped(Exception):pass

for root_index,(a,x) in enumerate(roots):
    Q=[[None]*6 for _ in range(6)]
    Q[0][0]=a
    for j,v in enumerate(x,1):Q[0][j]=Q[j][0]=v
    states=[0]
    matrices=[]
    def visit(i):
        if i==6:
            matrices.append([r[:] for r in Q]);return
        prefix=tuple(Q[i][:i])
        for diag,cross in by_prefix[i][prefix]:
            states[0]+=1
            if states[0]>100000 or time.monotonic()-began>=60:raise Capped
            Q[i][i]=diag
            for j in range(i+1,6):Q[i][j]=Q[j][i]=cross[j-1]
            if all(sum(Q[i][k]*Q[j][k] for k in range(6))<=13 for j in range(i)):
                visit(i+1)
            for j in range(i,6):Q[i][j]=Q[j][i]=None
    status='COMPLETE'
    try:visit(1)
    except Capped:status='UNKNOWN'
    cases.append(dict(root_index=root_index,diagonal=a,cross=x,status=status,
                      states=states[0],retained=len(matrices),global_start=len(all_matrices)))
    all_matrices.extend(matrices)
    if status=='UNKNOWN':break
result=dict(status='COMPLETE' if len(cases)==9 and all(c['status']=='COMPLETE' for c in cases) else 'UNKNOWN',
            profile_count=len(profiles),first_row_cases=len(roots),visited_cases=len(cases),
            unvisited_cases=len(roots)-len(cases),cases=cases,retained=len(all_matrices),
            seconds=time.monotonic()-began,limits={'states_per_first_row':100000,'aggregate_seconds':60},
            matrices=all_matrices,scope='necessary quotient matrices; no graph lift, CNF change, or solver verdict')
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='matrices'})
