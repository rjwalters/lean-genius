from pathlib import Path
import json,itertools as it,time,hashlib,sqlite3
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
names=['residual-ten-D5-five-311-center-structure','residual-ten-D5-five-311-structured-center-cover'];nh=0
for name in names:
 p=b/name
 for fn in ['pins.json','input-pins.json']:
  for k,v in read(p/fn).items():
   q=Path(k);q=q if q.is_absolute() else p/q
   assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2486,2488]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
d=read(b/names[0]/'results.json');sc=read(b/names[1]/'results.json');assert d['status']==sc['status']=='COMPLETE';start=time.monotonic();status='INCOMPLETE';tested=0;expected=set()
def guard():
 if time.monotonic()-start>30:raise TimeoutError
def graph(E):
 N=[set() for _ in range(10)]
 for i,j in E:assert i!=j;N[i].add(j);N[j].add(i)
 return N
try:
 allowed=[p for p in it.combinations(range(5),2) if not set(p)<={0,1,2}]
 for choice in it.combinations(allowed,4):
  for internal in it.combinations(list(it.combinations(range(5),2)),2):
   guard();cross={(x,5) for x in [0,1,2]}|{(x,6+j) for j,pair in enumerate(choice) for x in pair};E=cross|set(internal)
   if any(sum(v in e for e in E)!=3 for v in range(5)):continue
   for partner in [7,8,9]:
    rest=sorted({7,8,9}-{partner});full=E|{(6,partner),tuple(rest)};tested+=1;N=graph(full)
    assert all(len(ns)==3 for ns in N)
    if all(len(x&y)<=1 for x,y in it.combinations(N,2)):expected.add(tuple(sorted(full)))
 actual={tuple(map(tuple,r['edges'])) for r in d['records']};assert len(actual)==len(d['records'])==93 and expected==actual and tested==d['tested_degree_compatible']==171;status='COMPLETE'
except TimeoutError:pass
first={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'tested':tested,'graphs':len(expected)};(o/'stage1.json').write_text(json.dumps(first,indent=2)+'\n');print(first,flush=True);assert status=='COMPLETE'
domains={r['root']:r for r in read(b/'residual-ten-D5-five-311-center-domains/results.json')['records']};old=read(b/'residual-ten-D5-five-311-center-cover/results.json')['records'];models={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-orbit-capacity/models.json')['records']};edgecases={r['root']:r for r in read(b/'residual-ten-D5-five-311-low-edge-capacity/results.json')['records']};required={r['root'] for r in old if r['witness'] is not None};lookup={r['root']:r for r in sc['records']};assert len(lookup)==len(sc['records'])==len(required)==39 and lookup.keys()==required
start=time.monotonic();status='INCOMPLETE';verified=0
try:
 for key,r in lookup.items():
  guard();assert r['status']=='COMPLETE' and r['witness'] is not None;m=models[key];d=domains[key];lows=next(a['lows'] for a in edgecases[m['source_root']]['survivors'] if a['assignment']==m['assignment']);labels=[lows[i][0]//2 if lows[i][0]>=0 else -1 for i,j in d['low_orbits']]
  permitted=[]
  for g in d['low_groups']:
   act=[labels[i] for i in g if labels[i]>=0];inactive=sum(labels[i]<0 for i in g)
   if inactive<=1 and len(set(act))==len(act):permitted.append(frozenset(g))
  assert len(permitted)==r['low_options'];high,(low,E)=r['witness'];assert len(high)==5 and {i for i,m in high}==set(range(5)) and len(low)==5;used=set();Ay=[];z=0
  for i,mask in high:
   chosen=frozenset(j for j in range(25) if mask&(1<<j));assert mask==sum(1<<j for j in chosen) and chosen in set(map(frozenset,d['high_groups'][i])) and not chosen&used;used|=chosen
  for mask in low:
   chosen=frozenset(j for j in range(25) if mask&(1<<j));assert mask==sum(1<<j for j in chosen) and chosen in permitted and not chosen&used;used|=chosen;Ay.append({labels[j] for j in chosen if labels[j]>=0});z+=sum(labels[j]<0 for j in chosen)
  assert used==set(range(25)) and z==1 and len({tuple(sorted(e)) for e in E})==len(E)==15;N=graph(E);assert all(len(ns)==3 for ns in N) and all(len(x&y)<=1 for x,y in it.combinations(N,2))
  for j,active in enumerate(Ay):assert N[5+j]&set(range(5))==set(range(5))-active
  verified+=1
 assert verified==39;status='COMPLETE'
except TimeoutError:pass
second={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'verified_covers':verified};(o/'stage2.json').write_text(json.dumps(second,indent=2)+'\n');(o/'audit.json').write_text(json.dumps({'hashes':nh,'stages':[first,second]},indent=2)+'\n');print(second)
