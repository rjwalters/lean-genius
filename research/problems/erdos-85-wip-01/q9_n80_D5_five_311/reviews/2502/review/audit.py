from pathlib import Path
import json,itertools as I,time,hashlib,collections,sqlite3
p=Path(__file__).parent;b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');src=b/'residual-ten-D5-five-311-centered-propagation';read=lambda f:json.loads(f.read_text());hashes={}
for mf in ['pins.json','input-pins.json']:
 for n,h in read(src/mf).items():
  f=src/n;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;hashes[str(f)]=h
def dataset(name):return read(b/('residual-ten-D5-five-311-'+name)/'results.json')
def records(name):return dataset(name)['records']
def keyed(name):return {r['root']:r for r in records(name)}
configs=dataset('full-center-configurations');assert configs['status']=='COMPLETE';high=keyed('high-center-assignments');cross=keyed('center-cross-domains');original=keyed('center-domains');prop=keyed('low-propagation');edgecases=keyed('low-edge-capacity');joint=keyed('nonempty-joint');graphs=keyed('high-matchings');pack=records('packing');dom=read(b/'residual-ten-D5-supports/results.json')['records'];result=read(src/'results.json');assert result['status']=='COMPLETE';saved={r['root']:r for r in result['records']};assert len(saved)==len(result['records'])==len(configs['records'])==29 and set(saved)=={r['root'] for r in configs['records']}
start=time.monotonic();status='INCOMPLETE';out=[];forces=0;removals=collections.Counter()
try:
 for entry in configs['records']:
  rid=entry['root'];o=original[rid];source=joint[o['source_root']];ai=o['source_assignment'];ci=source['class'];lowdata=next(x for x in edgecases[o['source_root']]['survivors'] if x['assignment']==ai);lows=list(map(tuple,lowdata['lows']));assert len(lows)==50
  old=next(x for x in prop[o['source_root']]['survivors'] if x['assignment']==ai);root=pack[ci]['survivors'][source['source_root']];primary=[dom[ci]['high3'][j] for j in root['high3']];S=[set(t) for s in primary for t in (s,[e^1 for e in s])];R=[set() for _ in range(10)]
  for i,j in dom[ci]['edges']:R[i].add(j);R[j].add(i)
  expected=[(hc['high_assignment'],ki,cfg) for hc in entry['configs'] for ki,cfg in enumerate(hc['survivors'])];assert saved[rid]['status']=='COMPLETE';answers={(x['high_assignment'],x['center_config']):x for x in saved[rid]['records']};assert len(answers)==len(saved[rid]['records'])==len(expected) and set(answers)=={(h,k) for h,k,c in expected}
  for hi,ki,cfg in expected:
   if time.monotonic()-start>30:raise TimeoutError
   answer=answers[hi,ki];assert answer['status']=='NEGATIVE';colors={};h=high[rid]['survivors'][hi]
   for center,option in enumerate(h['high_options']):
    for orbit in cross[rid]['high_groups'][center][option]:
     for low in o['low_orbits'][orbit]:assert low not in colors;colors[low]=center
   for center,option in enumerate(cfg['low_options'],5):
    for orbit in cross[rid]['low_groups'][option]['orbits']:
     for low in o['low_orbits'][orbit]:assert low not in colors;colors[low]=center
   assert set(colors)==set(range(50));N=[set() for _ in range(80)]
   def edge(i,j):assert i!=j;N[i].add(j);N[j].add(i)
   for i in range(10):
    for j in R[i]:edge(i,j)
   for v,s in enumerate(S):
    for r in s:edge(10+v,r)
    edge(10+v,70+v//2)
   for v,w in graphs[source['packing_root']]['survivors'][source['graph']]['edges']:edge(10+v,10+w)
   for i,(v,r) in enumerate(lows):
    edge(20+i,r);edge(20+i,70+colors[i])
    if v>=0:edge(20+i,10+v)
   for i,j in cfg['center_edges']:edge(70+i,70+j)
   chosen=[set() for _ in lows];cand=[set() for _ in lows]
   for i,j in old['forced_edges']:edge(20+i,20+j);chosen[i].add(j);chosen[j].add(i)
   for i,j in old['remaining_edges']:cand[i].add(j);cand[j].add(i)
   assert all(len(N[i]&N[j])<=1 for i,j in I.combinations(range(80),2))
   goal=[6 if v>=0 else 7 for v,r in lows];rtarget=[set(range(10))-R[r]-(S[v] if v>=0 else set()) for v,r in lows];ctarget=[]
   for i,(v,r) in enumerate(lows):
    blocked={j-70 for j in N[70+colors[i]] if j>=70};target=set(range(10))-blocked
    if v>=0:assert v//2 in target;target.remove(v//2)
    assert len(target)==goal[i];ctarget.append(target)
   def view(i):
    usedr={lows[j][1] for j in chosen[i]};usedc={colors[j] for j in chosen[i]};byr=collections.defaultdict(list);byc=collections.defaultdict(list)
    for j in sorted(cand[i]):byr[lows[j][1]].append(j);byc[colors[j]].append(j)
    return usedr,usedc,goal[i]-len(chosen[i]),byr,byc
   def remove(i,j):assert j in cand[i] and i in cand[j];cand[i].remove(j);cand[j].remove(i)
   for step in answer['trace']:
    if 'removed' in step:
     for i,j,why in step['removed']:
      if why=='slot':
       ur,uc,slots,br,bc=view(i);assert lows[j][1] not in rtarget[i] or colors[j] not in ctarget[i] or lows[j][1] in ur or colors[j] in uc or slots==0
      else:
       assert why=='C4';u,v=20+i,20+j
       assert any(v in N[z] for y in N[u] for z in N[y] if z!=u and y!=v)
      remove(i,j);removals[why]+=1
    else:
     i,j=step['forced'];reason=step['reason'];assert reason['kind']=='required_singleton';ur,uc,slots,br,bc=view(i)
     if reason['type']=='center':required=ctarget[i]-uc;by=bc
     else:
      assert reason['type']=='residual';required=rtarget[i]-ur if lows[i][0]>=0 else set(br) if len(br)==slots else set();by=br
     assert reason['target'] in required and by[reason['target']]==[j]
     remove(i,j);chosen[i].add(j);chosen[j].add(i);edge(20+i,20+j);forces+=1
   cert=answer['certificate'];assert cert['kind']=='slot_shortage';i=cert['low'];ur,uc,slots,br,bc=view(i)
   assert slots<0 or len(ur)!=len(chosen[i]) or len(uc)!=len(chosen[i]) or len(br)<slots or not ctarget[i]-uc<=set(bc) or (lows[i][0]>=0 and not rtarget[i]-ur<=set(br))
   assert cert=={'kind':'slot_shortage','low':i,'slots':slots,'usedR':sorted(ur),'usedC':sorted(uc),'availableR':sorted(br),'availableC':sorted(bc)}
   assert answer['forced_edges']==[[i,j] for i in range(50) for j in sorted(chosen[i]) if i<j]
   out.append({'root':rid,'high_assignment':hi,'center_config':ki,'status':'NEGATIVE','shortage':cert})
 assert len(out)==706 and forces==1398;status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':hashes,'forces':forces,'removals':dict(removals),'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'hashes':len(hashes),'configs':len(out),'forces':forces,'removals':dict(removals)}))
