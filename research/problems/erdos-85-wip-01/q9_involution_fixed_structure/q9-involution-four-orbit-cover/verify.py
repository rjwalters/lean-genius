from pathlib import Path
import itertools,json
p=Path(__file__).resolve().parent;saved=json.loads((p/'matrices.json').read_text());positions=[(i,j) for i in range(4) for j in range(i,4)];pairs=list(itertools.combinations(range(4),2));expected={}
def allocations(total,k):
 if k==1:yield(total,);return
 for x in range(total+1):
  for tail in allocations(total-x,k-1):yield(x,*tail)
for m in range(7):
 for edges in itertools.combinations(pairs,m):
  for k in range(5):
   for loops in itertools.combinations(range(4),k):
    A=4+2*m+k
    if A>10 or any(u in loops and v in loops for u,v in edges):continue
    adj=[set() for _ in range(4)]
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    for u in loops:adj[u].add(u)
    caps=[2-len(adj[u]&adj[v]) for u,v in pairs]
    if min(caps)<0:continue
    cs={a for a in allocations(10-A,6) if all(x<=y for x,y in zip(a,caps))}
    if not cs:continue
    code=sum(1<<i for i,(u,v) in enumerate(positions) if v in adj[u]);expected[code]=(A,caps,cs)
assert len(saved)==len(expected)==243
for r in saved:
 A,caps,cs=expected[r['code']];assert A==r['A_count'] and caps==r['pair_capacities'] and cs==set(map(tuple,r['repeat_allocations']))
 seen=set();todo=[tuple(x for row in r['Q'] for x in row)];seen.add(todo[0])
 for flat in todo:
  for u in range(3):
   g=list(range(4));g[u],g[u+1]=g[u+1],g[u]
   z=tuple(flat[4*g[i]+g[j]] for i in range(4) for j in range(4))
   if z not in seen:seen.add(z);todo.append(z)
 r['canonical_check']=min(seen)
assert len({r['canonical_check'] for r in saved})==24
print('PASS: all243 quotients,4507 aggregate allocations,24 symmetry classes independently checked.')
