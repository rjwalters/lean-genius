from pathlib import Path
import json,itertools as it,hashlib,sqlite3,time
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');p=b/'residual-ten-D5-five-311-low-propagation';o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
nh=0
for name in ['pins.json','input-pins.json']:
 if not (p/name).exists():continue
 for k,v in read(p/name).items():
  q=Path(k);q=q if q.is_absolute() else p/q
  assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2473,2476]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
data=read(p/'results.json');assert data['status']=='COMPLETE'
prior=read(b/'residual-ten-D5-five-311-low-edge-capacity/results.json')['records'];joint={r['root']:r for r in read(b/'residual-ten-D5-five-311-nonempty-joint/results.json')['records']};graphs={r['root']:r for r in read(b/'residual-ten-D5-five-311-high-matchings/results.json')['records']};pack=read(b/'residual-ten-D5-five-311-packing/results.json')['records'];dom=read(b/'residual-ten-D5-supports/results.json')['records']
source={(r['root'],a['assignment']):a for r in prior for a in r['survivors']};output={(r['root'],a['assignment']):(a,negative) for r in data['records'] for negative,rows in [(True,r['certificates']),(False,r['survivors'])] for a in rows};assert len(source)==len(output)==142 and source.keys()==output.keys() and sum(len(r['certificates'])+len(r['survivors']) for r in data['records'])==142
start=time.monotonic();status='INCOMPLETE';neg=pos=nforced=0
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 for key,original in source.items():
  guard();rec,isnegative=output[key];src=joint[key[0]];ci=src['class'];d=dom[ci];root=pack[ci]['survivors'][src['source_root']];S=[]
  for j in root['high3']:
   s=set(d['high3'][j]);S.extend([s,{v^1 for v in s}])
  rho={v:w for a,z in d['edges'] for v,w in [(a,z),(z,a)]};lows=original['lows'];N=[set() for _ in range(70)]
  def edge(i,j):N[i].add(j);N[j].add(i)
  for i,j in d['edges']:edge(i,j)
  for v,s in enumerate(S):
   for r in s:edge(10+v,r)
  for i,j in graphs[src['packing_root']]['survivors'][src['graph']]['edges']:edge(10+i,10+j)
  for i,(v,r) in enumerate(lows):
   edge(20+i,r)
   if v>=0:edge(20+i,10+v)
  candidates={tuple(e) for e in original['allowed_edges']};chosen=set();goal=[6 if v>=0 else 7 for v,r in lows];targets=[set(range(10))-({rho[r]}|(S[v] if v>=0 else set())) for v,r in lows]
  def incident(edges,i):return {v if u==i else u for u,v in edges if u==i or v==i}
  def c4(i,j):return any(bb in N[aa] for aa in N[20+i] for bb in N[20+j])
  def state(i):
   neighbors=incident(chosen,i);used={lows[j][1] for j in neighbors};available=incident(candidates,i);groups={r:{j for j in available if lows[j][1]==r} for r in {lows[j][1] for j in available}}
   return neighbors,used,available,groups,goal[i]-len(neighbors)
  for step in rec['trace']:
   guard()
   if 'removed' in step:
    for i,j,reason in step['removed']:
     e=tuple(sorted((i,j)));assert e in candidates
     if reason=='C4':assert c4(i,j)
     else:
      assert reason=='support_or_degree';neighbors,used,_,_,_=state(i);assert len(neighbors)==goal[i] or lows[j][1] in used
     candidates.remove(e)
   else:
    i,j=step['forced'];e=tuple(sorted((i,j)));assert e in candidates and not c4(i,j)
    neighbors,used,available,groups,slots=state(i);reason=step['reason']
    assert slots==reason['slots'] and slots>0
    if reason['kind']=='required_singleton':
     r=reason['support'];required=targets[i]-used if lows[i][0]>=0 else set(groups) if len(groups)==slots else set()
     assert r in required and groups[r]=={j} and reason['available_supports']==len(groups)
    else:assert reason['kind']=='all_remaining_edges' and len(available)==slots
    candidates.remove(e);chosen.add(e);edge(20+i,20+j)
  assert chosen==set(map(tuple,rec['forced_edges'])) and len(chosen)==len(rec['forced_edges']);nforced+=len(chosen)
  if isnegative:
   assert rec['kind']=='support_shortage';i=rec['low'];neighbors,used,available,groups,slots=state(i)
   assert slots==rec['slots'] and sorted(used)==rec['used'] and sorted(groups)==rec['remaining_supports']
   assert slots<0 or len(used)!=len(neighbors) or len(groups)<slots or (lows[i][0]>=0 and not targets[i]-used<=set(groups));neg+=1
  else:
   assert candidates==set(map(tuple,rec['remaining_edges'])) and len(candidates)==len(rec['remaining_edges'])
   for i in range(50):
    neighbors,used,available,groups,slots=state(i);assert len(used)==len(neighbors) and slots>=0 and len(groups)>=slots
    if lows[i][0]>=0:assert targets[i]-used<=set(groups)
   assert all(not c4(i,j) for i,j in candidates);pos+=1
 assert (neg,pos,nforced)==(48,94,1618);status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':nh,'negative':neg,'positive':pos,'forced_edges':nforced};(o/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
