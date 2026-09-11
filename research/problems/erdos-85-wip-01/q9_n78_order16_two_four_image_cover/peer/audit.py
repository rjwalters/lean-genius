from pathlib import Path
import itertools as I,json,hashlib,sqlite3,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-order16-two-four-image-cover');read=lambda f:json.loads(f.read_text());checks={}
for mf in [src/'pins.json',src/'input-pins.json']:
 for name,h in read(mf).items():
  f=mf.parent/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;checks[str(f)]=h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
states=[dict(c.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2419,2438]];assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in states)
saved=read(src/'results.json');assert saved['status']=='COMPLETE'
start=time.monotonic();subgroups=[];models=[];rejected=[];status='INCOMPLETE'
try:
 # Reconstruct the ambient set directly as all matching-preserving permutations.
 matching={frozenset((0,2)),frozenset((1,3))}
 four=[g for g in I.permutations(range(4)) if {frozenset(g[x] for x in e) for e in matching}==matching]
 permutations={tuple([z,z^1]+[v+2 for v in g]) for z in range(2) for g in four}
 assert len(permutations)==16 and permutations==set(map(tuple,saved['ambient_action']))
 order=list(map(tuple,saved['ambient_action']));index={g:i for i,g in enumerate(order)}
 M=[[index[tuple(a[b[v]] for v in range(6))] for b in order] for a in order];assert M==saved['multiplication']
 assert order[0]==tuple(range(6))
 for subset in range(1<<15):
  if time.monotonic()-start>30:raise TimeoutError
  bits=(subset<<1)|1;n=bits.bit_count()
  if n not in (1,2,4,8,16):continue
  H=[v for v in range(16) if bits>>v&1]
  if any(not (bits>>M[a][b]&1) for a in H for b in H):continue
  subgroups.append(H)
  if n not in (4,8) or {order[g][0] for g in H}!={0,1} or {order[g][2] for g in H}!={2,3,4,5}:continue
  inv=[g for g in H if g!=0 and M[g][g]==0 and order[g][0]==1]
  r={'elements':H,'order':n,'involutions_swapping_two':inv}
  if inv:models.append(r)
  else:rejected.append(r)
 assert set(map(tuple,subgroups))==set(map(tuple,saved['all_subgroups'])) and len(subgroups)==35
 for actual,claimed in [(models,saved['models']),(rejected,saved['excluded_no_involution'])]:
  amap={tuple(r['elements']):r for r in actual};cmap={tuple(r['elements']):r for r in claimed};assert len(amap)==len(actual)==len(cmap)==len(claimed) and set(amap)==set(cmap)
  for key,r in amap.items():assert r['order']==cmap[key]['order'] and set(r['involutions_swapping_two'])==set(cmap[key]['involutions_swapping_two'])
 types={}
 for r in models:
  H=r['elements'];proj={order[g][2:] for g in H}
  if len(H)==4:
   assert len(proj)==4 and all(M[g][g]==0 for g in H);label='graph_V4'
  elif len(proj)==8:label='graph_D8'
  else:
   assert len(proj)==4 and any(order[g][:2]==(1,0) and order[g][2:]==(2,3,4,5) for g in H)
   label='product_C4' if any(M[g][g]!=0 for g in H) else 'product_V4'
  types[label]=types.get(label,0)+1
 assert types=={'graph_V4':3,'graph_D8':3,'product_C4':1,'product_V4':1}
 assert len(rejected)==1 and len(rejected[0]['elements'])==4 and any(M[g][g]!=0 for g in rejected[0]['elements'])
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':checks,'premises':states,'subgroups':subgroups,'models':models,'excluded':rejected,'types':types if status=='COMPLETE' else None}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'hashes':len(checks),'subgroups':len(subgroups),'models':len(models),'types':r['types']}))
