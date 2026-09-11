from pathlib import Path
import itertools as it,json,hashlib,time
out=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/residual-ten-11123-supports')
for n,h in json.loads((src/'pins.json').read_text()).items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==h
saved=json.loads((src/'results.json').read_text());classes=json.loads((src/'classes.json').read_text())
expected={tuple(map(tuple,r['edges'])):set(map(tuple,r['supports'])) for r in saved['records']}
blocks=[(i,i) for i in range(5)]+list(it.combinations(range(5),2));target=[1,1,1,2,3];degree=[0]*5;graphs=[];skeletons=set();start=time.monotonic()
def walk(k,edges,skeleton):
 if time.monotonic()-start>30:raise TimeoutError('UNKNOWN original30s')
 if k==15:
  if degree==target:graphs.append(tuple(sorted(edges)));skeletons.add(tuple(skeleton))
  return
 i,j=blocks[k]
 walk(k+1,edges,skeleton+[0])
 if degree[i]>=target[i] or degree[j]>=target[j]:return
 degree[i]+=1
 if j!=i:degree[j]+=1
 if i==j:walk(k+1,edges+[(2*i,2*i+1)],skeleton+[1])
 else:
  for s in range(2):walk(k+1,edges+[(2*i,2*j+s),(2*i+1,2*j+(1^s))],skeleton+[1])
 degree[i]-=1
 if j!=i:degree[j]-=1
walk(0,[],[])
def valid(edges,n):
 mids={}
 adj=[set() for _ in range(n)]
 for a,b in edges:adj[a].add(b);adj[b].add(a)
 for z,row in enumerate(adj):
  for pair in it.combinations(sorted(row),2):
   if pair in mids:return None
   mids[pair]=z
 return adj
actual={}
for edges in graphs:
 adj=valid(edges,10)
 if adj is None:continue
 supports=set()
 for ids in it.combinations(range(5),3):
  for bits in it.product(range(2),repeat=3):
   T=tuple(2*i+b for i,b in zip(ids,bits));other=tuple(t^1 for t in T)
   if T>other or sum(target[i] for i in ids)>5:continue
   if len(set.union(*(adj[t] for t in T))&set(range(6)))>1:continue
   if valid(list(edges)+[(t,10) for t in T]+[(t,11) for t in other],12) is not None:supports.add(T)
 actual[edges]=supports
assert actual==expected
# Compute each saved representative's full orbit and partition the reconstructed set.
covered=set();counts=[]
for C in classes['classes']:
 orbit=set()
 for perm in it.permutations(range(3)):
  axes=perm+(3,4)
  for bits in it.product(range(2),repeat=5):
   def tr(v):return 2*axes[v//2]+((v%2)^bits[v//2])
   orbit.add(tuple(sorted(tuple(sorted((tr(a),tr(b)))) for a,b in C['representative_edges'])))
 assert not covered&orbit and orbit<=set(actual)
 assert len(orbit)==C['labelled_count']
 assert set(map(tuple,C['support_orbits']))==actual[tuple(map(tuple,C['representative_edges']))]
 covered|=orbit;counts.append(len(orbit))
assert covered==set(actual)
result=dict(status='COMPLETE',cap_seconds=30,seconds=time.monotonic()-start,skeletons=len(skeletons),degree_graphs=len(graphs),graphs=len(actual),supports=sum(map(len,actual.values())),class_counts_in_saved_order=counts,paper_order_typo=True)
out.joinpath('audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
