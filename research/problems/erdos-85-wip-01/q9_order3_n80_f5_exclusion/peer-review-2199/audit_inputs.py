from pathlib import Path
import itertools, json
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-word-support-cover')
ps=list(itertools.permutations(range(3)))
words=list(itertools.product(range(3),repeat=5))
E=[[0,0,0],[0,0,1],[0,1,0]]
tables=[]
for a,b,c,d in itertools.product(range(5),repeat=4):
    t=[[a,b,4-a-b],[c,d,3-c-d],[4-a-c,3-b-d,a+b+c+d-4]]
    if all(x>=0 for row in t for x in row): tables.append(t)
assert len(tables)==65
mats=[[[int(perm[a]==b) for b in range(3)] for a in range(3)] for perm in ps]
capacities=[]
allowed=[]
for direct,*paths in itertools.product(range(6),repeat=4):
    P=mats[direct]
    cap=[[3-sum(E[a][k]*P[k][b]+P[a][k]*E[k][b] for k in range(3))
          -sum(mats[z][a][b] for z in paths) for b in range(3)] for a in range(3)]
    capacities.append(cap)
    allowed.append(int(any(all(t[a][b]<=cap[a][b] for a in range(3) for b in range(3)) for t in tables)))
expected=allowed[:]
for u,v in itertools.combinations(range(5),2):
    for cap in capacities:
        bits=sum(1<<i for i,w in enumerate(words) if cap[w[u]][w[v]]>0)
        expected.extend((bits>>(64*j))&((1<<64)-1) for j in range(4))
for u in range(5):
    for a in range(3):
        bits=sum(1<<i for i,w in enumerate(words) if w[u]==a)
        expected.extend((bits>>(64*j))&((1<<64)-1) for j in range(4))
assert expected==list(map(int,(s/'input.txt').read_text().split()))
print(json.dumps({'integers_verified':len(expected),'tables':len(tables),'allowed':sum(allowed)}))
