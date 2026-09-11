import itertools,json,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parent
src=BASE/'q9-involution-n80-t01-incidence/results.json'
graphs=json.loads((BASE/'q9-involution-n80-degree-five-centers/representatives.json').read_text())
start=time.monotonic();out=[]
for index,case in enumerate(json.loads(src.read_text())['results'][:24]):
 Y=case['witness'];P=set(case['case']['P']);delta=[2-sum(y) for y in Y]
 if any(delta[f]==0 for f in P):continue
 H=[set() for _ in range(10)]
 for a,b in graphs[case['case']['graph_index']]['edges']:H[a].add(b);H[b].add(a)
 # The first orbit of every P group is its central degree-two orbit.
 owners=sorted(P)+[f for f in range(10) for _ in range(delta[f]-int(f in P))]
 assert len(owners)==6
 T0=[1+delta[f]-len(H[f]&P) for f in range(10)]
 target_assignments=[]
 for targets in set(itertools.permutations(tuple(f for f in range(10) for _ in range(delta[f])))):
  if any(q in H[p] for p,q in zip(owners,targets)):continue
  if [targets[:4].count(f) for f in range(10)]!=T0:continue
  Z=[[0]*10 for _ in range(10)]
  for p,q in zip(owners,targets):Z[p][q]+=1
  if any(Z[p][q]!=Z[q][p] for p in range(10) for q in range(10)):continue
  target_assignments.append(targets)
 # Enumerate central leaf bijections, then the remaining two k2 orbit supports.
 tested=0;first=None
 for leaves in itertools.permutations(range(1,5)):
  supports=[{0,j} for j in leaves]
  if any(any(Y[f][j] for j in S) for f,S in zip(owners[:4],supports)):continue
  options=[]
  for f in owners[4:]:
   used=set().union(*(S for owner,S in zip(owners[:4],supports) if owner==f))
   options.append(list(itertools.combinations([j for j in range(1,5) if not Y[f][j] and j not in used],2)))
  for rest in itertools.product(*options):
   SS=supports+list(map(set,rest))
   if any(SS[4]&SS[5]) and owners[4]==owners[5]:continue
   for targets in target_assignments:
    assert time.monotonic()-start<30,'INCOMPLETE30s; no retry'
    tested+=1
    T=[[0]*5 for _ in range(10)]
    for q,S in zip(targets,SS):
     for j in S:T[q][j]+=1
    if any(sum(Y[g][j] for g in H[f])> (sum(Y[f]) if j==0 else Y[f][0])+T[f][j] for f in range(10) for j in range(5)):continue
    first=dict(owners=owners,targets=list(targets),supports=[sorted(S) for S in SS]);break
   if first:break
  if first:break
 out.append(dict(root_index=index,target_assignments=len(target_assignments),tested=tested,status='WITNESS' if first else 'REJECTED_SAVED_MATRIX',witness=first))
result=dict(status='COMPLETE',seconds=time.monotonic()-start,scope='Filters only ten saved t0 incidence matrices; no full-root exclusion or old search retry',results=out)
(ROOT/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
