import json,hashlib,itertools,sqlite3
from pathlib import Path
base=Path('/Users/rwalters/lean-genius-q9-known-values-20260911')
sources={2265:Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n80-residual-five-t2'),2266:Path('/tmp/erdos85-sol1-q9-n78-regular-eight-exceptional'),2268:Path('/tmp/erdos85-sol1-q9-n78-three-orbit-stabilizers')}
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for rid,p in sources.items():
 out=base/f'review-{rid}';out.mkdir(exist_ok=True)
 pins=json.loads((p/'pins.json').read_text())
 for f,h in pins.items():assert sha(p/f)==h,f
 premises=[]
 for name in ['premise.json','premises.json','accepted-premises.json']:
  if (p/name).exists():
   data=json.loads((p/name).read_text());data=data if isinstance(data,list) else [data]
   for v in data:
    i=v.get('review',v.get('id'));state=db.execute('select status,resolution from review_requests where id=?',(i,)).fetchone();assert state[0]=='resolved' and state[1].startswith('PASS'),(i,state)
    if 'source' in v:assert sha(Path(v['source']))==v['sha256']
    premises.append(i)
 external=0
 if (p/'input-pins.json').exists():
  for f,h in json.loads((p/'input-pins.json').read_text()).items():assert sha(Path(f))==h;external+=1
 result={'review':rid,'pins_verified':len(pins),'external_pins':external,'accepted_premises':premises}
 if rid==2266:
  edges=list(itertools.combinations(range(4),2));found=[]
  for mask in range(64):
   es={e for i,e in enumerate(edges) if mask>>i&1};nb=[{y for x,y in es if x==v}|{x for x,y in es if y==v} for v in range(4)]
   if min(map(len,nb))<1 or any(len(nb[u]&nb[v])>1 for u,v in edges):continue
   aut=sum({tuple(sorted((perm[u],perm[v]))) for u,v in es}==es for perm in itertools.permutations(range(4)))
   typ={(1,1,1,1):'matching',(1,1,2,2):'path',(1,1,1,3):'star',(1,2,2,3):'triangle_pendant'}[tuple(sorted(map(len,nb)))]
   part=aut&-aut
   assert typ=='matching' or part<=2
   found.append({'mask':mask,'type':typ,'automorphisms':aut,'two_part':part})
  assert found==json.loads((p/'results.json').read_text())['cases']
  result.update(masks=64,permutations_per_mask=24,survivors=len(found),cases=found)
 if rid==2265:
  reps=json.loads((p/'representatives.json').read_text());actual=[]
  for idx,g in enumerate(reps):
   nb=[set() for _ in range(10)]
   for u,v in g['edges']:nb[u].add(v);nb[v].add(u)
   assert all(len(n)==3 for n in nb) and all(len(nb[u]&nb[v])<=1 for u,v in itertools.combinations(range(10),2))
   for ps in itertools.combinations(range(10),4):
    P=set(ps);ds=[len(n&P) for n in nb]
    if sorted(ds)==[1]*8+[2]*2:kind='two211'
    elif sorted(ds)==[1]*9+[3]:kind='one221'
    else:continue
    special=[v for v,d in enumerate(ds) if d>1]
    if kind=='one221' and special[0] not in P:continue
    if kind=='two211':
     M=set(range(10))-P
     assert all(ds[v]==1 for v in P) and not P.intersection(special)
     assert sorted(len(nb[v]&M) for v in M)==[1,1,2,2,2,2]
     reached={min(M)}
     while True:
      nxt=reached|set.union(*(nb[v]&M for v in reached))
      if nxt==reached:break
      reached=nxt
     assert reached==M
    actual.append((idx,ps,tuple(special),kind))
  expected=[(v['graph_index'],tuple(v['P']),tuple(v['special']),v['kind']) for v in json.loads((p/'results.json').read_text())['retained']]
  assert actual==expected, (actual,expected)
  assert sum(v[3]=='two211' for v in actual)==9
  result.update(marked_pairs=630,retained=actual)
 (out/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
 (out/'source-pins.json').write_text(json.dumps({str(p/f):h for f,h in pins.items()},indent=2)+'\n')
 print(rid,'PASS',len(pins),'pins',result.get('survivors',result.get('marked_pairs','paper')))
