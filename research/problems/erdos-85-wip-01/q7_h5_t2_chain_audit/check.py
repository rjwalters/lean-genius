from pathlib import Path
import json,hashlib,itertools,sys
b=Path(sys.argv[1]);out=Path(__file__).parent
pins={}
def read(name):
 p=b/name;pins[name]=hashlib.sha256(p.read_bytes()).hexdigest();return json.loads(p.read_text())
src=read('q7_h5_heavy_core/core-t2.json');masks=src['masks'];edges=list(itertools.combinations(range(6),2))
assert masks==[7,25,10,18,12,20] and src['complete'] and src['stop'] is None
trans=[]
for perm in itertools.permutations(range(5)):
 ms=[sum(1<<perm[c] for c in range(5) if m>>c&1) for m in masks]
 if set(ms)==set(masks):
  hp=[masks.index(m) for m in ms]
  trans.append([edges.index(tuple(sorted((hp[a],hp[b])))) for a,b in edges])
labelled=[];canonical=set()
for bits in range(1<<15):
 g=[set() for _ in range(11)]
 for h,m in enumerate(masks):
  for c in range(5):
   if m>>c&1:g[c].add(5+h);g[5+h].add(c)
 for i,(a,d) in enumerate(edges):
  if bits>>i&1:g[5+a].add(5+d);g[5+d].add(5+a)
 if any(len(g[a]&g[d])>1 for a,d in itertools.combinations(range(11),2)):continue
 ok=True
 for h,m in enumerate(masks):
  guests=[v-5 for v in g[5+h] if v>=5];w=sum(masks[v].bit_count() for v in guests);d=len(guests);t=m.bit_count()
  if w>5 or t+d>7 or 2-t+w-d<0:ok=False;break
 if not ok:continue
 labelled.append(bits)
 canonical.add(min(sum(1<<tr[i] for i in range(15) if bits>>i&1) for tr in trans))
assert sorted(canonical)==src['canonical_cores'] and len(labelled)==src['labeled']
single=read('q7_h5_heavy_core/singleton-t2.json');empty=read('q7_h5_t2_integrated_empty/results.json');core210=read('q7_h5_t2_core210/search-results.json');adj=read('q7_h5_t2_adjacent_triples/result.json')
a=[r['core'] for r in single['results'] if r['status']=='EXCLUDED_SINGLETON_COMPLETION']
c=[r['core'] for r in empty['results'] if r['status']=='EXCLUDED_EMPTY_INCIDENCE']
d=[r['core'] for r in core210['results'] if r['status']=='EXHAUSTED']
e=adj['adjacent_open_cores']
assert a==[36,48,513,656,2049] and c==[1,2120] and d==[210] and e==[1537,6145,9217,9729]
assert single['source_sha256']==pins['q7_h5_heavy_core/core-t2.json']==adj['source_sha256']
assert single['unvisited']==empty['unvisited']==0 and core210['visited']==core210['total_patterns']==1
stages=[(2026,a,'q7_h5_heavy_core/review2026.json'),(2035,c,'q7_h5_t2_integrated_empty/review2035.json'),(2041,d,'q7_h5_t2_core210/review2041.json'),(2045,e,'q7_h5_t2_adjacent_triples/REVIEW2045.json')]
left=set(canonical);rows=[]
for review,removed,path in stages:
 r=read(path);assert r['id']==review and r['status']=='resolved' and r['resolution'].startswith('PASS')
 assert len(set(removed))==len(removed) and set(removed)<=left
 before=sorted(left);left-=set(removed)
 rows.append(dict(review=review,before=before,excluded=removed,after=sorted(left),review_file=path))
assert left=={44} and sum(len(x[1]) for x in stages)==12
for directory,manifest in [('q7_h5_heavy_core','singleton-source-pins.json'),('q7_h5_t2_integrated_empty','source-pins.json'),('q7_h5_t2_core210','source-pins.json'),('q7_h5_t2_adjacent_triples','pins.json')]:
 for f,h in read(directory+'/'+manifest).items():
  p=b/directory/f
  assert p.is_file(),str(p)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h,(str(p),h)
  pins[str(p.relative_to(b))]=h
result=dict(status='PASS',scope='Exact T2 heavy-core census and reviewed reduction accounting only; no new core44 exclusion or Lean proof.',direct_graphs_examined=32768,labelled=len(labelled),automorphisms=len(trans),canonical_cores=sorted(canonical),stages=rows,remaining=sorted(left),historical_caps_preserved=True,source_pins=pins)
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='source_pins'},indent=2))
