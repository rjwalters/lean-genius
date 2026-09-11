from pathlib import Path
import json,hashlib,sqlite3
p=Path(__file__).parent;s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-n78-m13-difference-constraints');base=s.parent/'q9-n78-m13-quotient'
for d in [s,base]:
 for f,h in json.loads((d/'pins.json').read_text()).items():assert hashlib.sha256((d/f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for id in [2140,2153]:
 r=dict(c.execute('select * from review_requests where id=?',(id,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');(p/f'premise-{id}.json').write_text(json.dumps(r,indent=2)+'\n')
a,b=json.loads((base/'verification.json').read_text())['representatives']
for q in [a,b]:assert all(sum(q[i][k]*q[j][k] for k in range(6))==(21 if i==j else 12) for i in range(6) for j in range(6))
def components(adj):
 left=set(range(6));out=[]
 while left:
  todo=[min(left)];seen=set()
  while todo:
   v=todo.pop()
   if v in seen:continue
   seen.add(v);todo.extend(adj[v]-seen)
  out.append(sorted(seen));left-=seen
 return out
triples=[{j for j in range(6) if a[i][j]==3} for i in range(6)];assert all(len(x)==2 for x in triples)
cs=components(triples);assert sorted(map(len,cs))==[3,3]
z=[{j for j in range(6) if j!=i and b[i][j]==0} for i in range(6)];assert all(len(x)==2 for x in z) and len(components(z))==1
assert all(not(z[i]&z[j]) for i in range(6) for j in z[i])
def pairs(left):
 if not left:return [()]
 i=min(left);return [((i,j),)+m for j in sorted(z[i]&left) for m in pairs(left-{i,j})]
ms=pairs(set(range(6)));assert len(ms)==2
source=json.loads((s/'results.json').read_text());assert {tuple(sorted(map(tuple,m))) for m in source['type_b_shift_pairings']}=={tuple(sorted(m)) for m in ms}
assert len({min((2*s)%13,(-2*s)%13) for s in range(1,7)})==6
out=dict(status='PASS',type_a_components=cs,type_b_connected_cycle=True,shift_pairings=ms)
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');(p/'source-pins.json').write_text((s/'pins.json').read_text());print(out)
