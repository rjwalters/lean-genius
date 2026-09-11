from pathlib import Path
import json,hashlib,itertools,datetime
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls/runs/004-N63-m7');meta=json.loads((src/'generator-metadata.json').read_text());result=json.loads((src/'result.json').read_text());assert (result['n'],result['d'],result['m'],result['status'])==(63,8,7,'SAT')
for name,k in [('input.cnf','cnf'),('generator-metadata.json','metadata'),('solver.log','output')]:assert hashlib.sha256((src/name).read_bytes()).hexdigest()==result[k]['sha256']
truth={}
for line in (src/'solver.log').read_text().splitlines():
 if line.startswith('v '):
  for lit in map(int,line[2:].split()):
   if lit:assert abs(lit) not in truth or truth[abs(lit)]==(lit>0);truth[abs(lit)]=lit>0
assert set(truth)==set(range(1,meta['variables']+1));clauses=[];current=[]
for line in (src/'input.cnf').read_text().splitlines():
 if not line or line[0] in 'cp':continue
 for lit in map(int,line.split()):
  if lit:current.append(lit)
  else:assert any(truth[abs(t)]==(t>0) for t in current);clauses.append(len(current));current=[]
assert not current and len(clauses)==134146
A=[[0]*63 for _ in range(63)];covered=set()
for orbit in meta['orbits']:
 edges={tuple(e) for e in orbit['edges']};u,v=min(edges);expected={tuple(sorted((7*(u//7)+(u+k)%7,7*(v//7)+(v+k)%7))) for k in range(7)};assert edges==expected;assert not covered&edges;covered|=edges
 if truth[orbit['var']]:
  for u,v in edges:A[u][v]=A[v][u]=1
assert covered==set(itertools.combinations(range(63),2));assert all(sum(row)==8 for row in A);assert all(A[i][i]==0 for i in range(63))
# Integer matrix trace, independently of the decoder's common-neighbor rejection.
B=[[sum(A[i][k]*A[k][j] for k in range(63)) for j in range(63)] for i in range(63)];trace4=sum(B[i][j]*B[j][i] for i in range(63) for j in range(63));assert trace4==63*8*15==7560
shift=[7*(v//7)+(v+1)%7 for v in range(63)];assert all(A[shift[u]][shift[v]]==A[u][v] for u in range(63) for v in range(63));seen=set();cycles=[]
for v in range(63):
 if v in seen:continue
 cycle=[];u=v
 while u not in cycle:cycle.append(u);seen.add(u);u=shift[u]
 assert u==v and len(cycle)==7;cycles.append(cycle)
assert len(cycles)==9
actual=json.loads((p/'graph.json').read_text());assert actual['adjacency']==[[j for j in range(63) if A[i][j]] for i in range(63)]
receipt=dict(status='PASS',n=63,edges=252,degree=8,trace_A4=trace4,c4_count=(trace4-63*8*15)//8,automorphism_cycles=cycles,clauses_checked=len(clauses),variables_checked=len(truth),graph_sha256=hashlib.sha256((p/'graph.json').read_bytes()).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Independent full terminal CNF/model and decoded control graph check; not a q9 witness.')
(p/'independent-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
