import pathlib,json,itertools,hashlib,sqlite3,time
P=pathlib.Path(__file__).parent; A=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a7-cycle-pairing-cover');B=P.parent/'h7-a7-cycle-colouring-cover'
read=lambda p:json.loads(p.read_text())
pins=read(A/'pins.json')
for f,h in pins.items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in read(A/'premises.json'):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());live['refs']=json.loads(live['refs']);old.pop('expired',None);assert old==live and live['resolution'].startswith('PASS')
ap=read(A/'results.json')['cases'];ac=read(A/'colour-results.json')['cases'];bp=read(B/'partition-results.json')['results'];bc=read(B/'colouring-results.json')['results'];K=list(itertools.combinations(range(7),2));ki={e:i for i,e in enumerate(K)};out=[];start=time.monotonic()
for a,x,b,y in zip(ap,ac,bp,bc):
 assert a['Q_edges']==b['Q_edges'] and a['raw_partitions']==b['raw_partitions']
 Q=list(map(tuple,a['Q_edges']));qi={e:i for i,e in enumerate(Q)};R=set(map(tuple,a['R_edges']));acts=[]
 for p in itertools.permutations(range(7)):
  if {tuple(sorted((p[u],p[v]))) for u,v in R}==R:acts.append([qi[tuple(sorted((p[u],p[v])))] for u,v in Q])
 own={tuple(r['blocks']):i for i,r in enumerate(b['representatives'])};maps={};stabs={}
 for i,r in enumerate(a['representatives']):
  masks=[sum(1<<e for e in block) for block in r['blocks']]
  for act in acts:
   moved=[sum(1<<act[e] for e in range(14) if m>>e&1) for m in masks];key=tuple(sorted(moved))
   if key in own:
    j=own[key];maps[i]=(j,[key.index(m) for m in moved]);assert r['orbit_size']==b['representatives'][j]['orbit_size'];break
  else:raise AssertionError('partition missing')
 assert len(set(j for j,p in maps.values()))==len(own)
 for blocks,j in own.items():
  stab=[]
  for act in acts:
   moved=[sum(1<<act[e] for e in range(14) if m>>e&1) for m in blocks]
   if set(moved)==set(blocks):stab.append([blocks.index(m) for m in moved])
  stabs[j]=stab
 converted={}
 for r in x['representatives']:
  j,p=maps[r['pairing_index']];cy=[p[v] for v in r['block_cycle']]
  canon=min(sum(1<<ki[tuple(sorted((s[cy[k]],s[cy[(k+1)%7]])))] for k in range(7)) for s in stabs[j])
  key=(j,canon);assert key not in converted;converted[key]=(r['cyclic_orbit_size'],r['full_labelled_orbit_size'])
 expected={(r['partition_index'],r['empty_cycle']):(r['cycle_orbit_size'],14*r['combined_orbit_size']) for r in y['normal_forms']}
 assert converted==expected
 out.append(dict(partitions=len(own),colourings=len(converted),labelled=sum(v[1] for v in converted.values())))
result=dict(status='PASS',cases=out,pins=len(pins),seconds=time.monotonic()-start,scope='Independent bitmask cover compared under explicit high and block relabellings; exact representative/orbit equality. Only F=C7 proper colourings.')
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
