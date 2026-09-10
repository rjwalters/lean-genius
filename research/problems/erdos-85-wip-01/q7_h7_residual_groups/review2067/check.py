from pathlib import Path
import json,hashlib,itertools
p=Path(__file__).parent;s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-residual-groups');pins=json.loads((s/'pins.json').read_text());assert all(hashlib.sha256((s/f).read_bytes()).hexdigest()==h for f,h in pins.items())
source=Path('/tmp/erdos85-sol1-h7-pair-host-reduction/results.json');samples=json.loads(source.read_text())['results'];out=[]
for sample in samples:
 g=list(map(set,sample['adjacency']));high=set(range(7));H=sorted(g[0]);hosts=set(H);outside=set(range(7,49))-hosts
 assert len(H)==8 and len(outside)==34
 assert all(len(g[u]&g[v])<=1 for u,v in itertools.combinations(range(49),2))
 weights={v:len(g[v]&high) for v in range(7,49)}
 mate={h:next(iter(g[h]&hosts)) for h in H};groups={h:sorted(g[h]&outside) for h in H}
 assert all(len(g[h]&hosts)==1 and mate[mate[h]]==h and len(groups[h])==6-weights[h] and len(g[h])==7 for h in H)
 assert set().union(*(set(vs) for vs in groups.values()))==outside and sum(map(len,groups.values()))==34
 pairhost={j:next(h for h in H if g[h]&high=={0,j}) for j in range(1,7)}
 allowed={}
 for h,vs in groups.items():
  for u in vs:
   forbidden={mate[h]}|{pairhost[j] for j in g[u]&high}
   assert len(forbidden)==1+weights[u]
   allowed[u]=hosts-forbidden
   assert len(allowed[u])==7-weights[u]
   assert len(g[u])==weights[u]+1
 A=[[sum(k in allowed[u] for u in groups[h]) for k in H] for h in H]
 for i,h in enumerate(H):
  for j,k in enumerate(H):assert A[i][j]==(0 if mate[h]==k else 7-weights[h]-weights[k])==A[j][i]
  assert A[i][i] in (3,5) and A[i][i]==7-2*weights[h]
  incoming=sum(k==h for u in outside for k in allowed[u]);demand=sum(6-weights[v] for v in groups[h])
  assert incoming-demand==len(groups[h])
 out.append(dict(twins_adjacent=sample['twins_adjacent'],group_sizes=[len(groups[h]) for h in H],availability=A,column_deficits=[len(groups[h]) for h in H]))
result=dict(status='PASS',samples=out,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),author_pins=pins,scope='Independent audit on different sample host assignments; universal defect conclusions follow conditional on full completion, no completed defect matrix asserted.')
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS two independent samples: forbidden-group counts, symmetric A, odd diagonals, exact column deficits')
