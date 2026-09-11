from pathlib import Path
import itertools as I,json,hashlib,sqlite3,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-central-kernel-two-residual-domain')
read=lambda f:json.loads(f.read_text());checks={}
for manifest in [src/'pins.json',src/'input-pins.json']:
 for name,h in read(manifest).items():
  f=manifest.parent/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;checks[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
premises=[dict(con.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2430,2434]]
assert all(x['status']=='resolved' and x['resolution'].startswith('PASS') for x in premises)
models=read(src.parent/'n78-central-kernel-two-group-cover/results.json')['models'];author=read(src/'results.json');assert author['status']=='COMPLETE'
claimed={r['model']:r for r in author['records']};assert len(claimed)==len(author['records'])==24 and set(claimed)==set(range(24))
def allmatchings(vertices):
 if not vertices:yield frozenset();return
 a=vertices[0]
 for j in range(1,len(vertices)):
  b=vertices[j]
  for rest in allmatchings(vertices[1:j]+vertices[j+1:]):yield rest|{(a,b)}
matchings=list(allmatchings(tuple(range(8))));assert len(matchings)==105
start=time.monotonic();records=[];status='INCOMPLETE'
try:
 for mi,m in enumerate(models):
  if time.monotonic()-start>30:raise TimeoutError
  M=m['multiplication'];A=m['X_action'];inv=m['inverse'];saved=claimed[mi];assert saved['status']=='COMPLETE'
  invariant=[e for e in matchings if all(frozenset(tuple(sorted((g[a],g[b]))) for a,b in e)==e for g in A)]
  savedmatch=[frozenset(map(tuple,e)) for e in saved['matchings']]
  assert len(invariant)==len(savedmatch) and set(invariant)==set(savedmatch)
  connections=[(a,b) for a,b in I.combinations(range(1,16),2) if {inv[a],inv[b]}=={a,b}]
  assert [list(x) for x in connections]==saved['connections']
  positives={(r['matching'],r['connection'],r['origin']):r for r in saved['survivors']};assert len(positives)==len(saved['survivors'])
  found=set();tested=0;badcerts=[]
  for ei,matching in enumerate(savedmatch):
   for di,(a,b) in enumerate(connections):
    for origin in range(8):
     if time.monotonic()-start>30:raise TimeoutError
     adj=[set() for _ in range(24)]
     for x,y in matching:adj[x].add(y);adj[y].add(x)
     for g in range(16):
      x=A[g][origin];adj[x].add(8+g);adj[8+g].add(x)
      adj[8+g].update([8+M[g][a],8+M[g][b]])
     assert all(len(ns)==3 and v not in ns and all(v in adj[w] for w in ns) for v,ns in enumerate(adj))
     key=(ei,di,origin);tested+=1;seen={};bad=None
     for center,ns in enumerate(adj):
      for ends in I.combinations(sorted(ns),2):
       if ends in seen:bad=[*ends,seen[ends],center];break
       seen[ends]=center
      if bad:break
     if bad:assert key not in positives;badcerts.append({'key':key,'C4':bad})
     else:
      assert key in positives
      edges=[[v,w] for v,ns in enumerate(adj) for w in sorted(ns) if v<w]
      assert edges==positives[key]['edges'];found.add(key)
  assert tested==saved['tested'] and found==set(positives)
  records.append({'model':mi,'matchings':len(invariant),'connections':len(connections),'tested':tested,'positives':len(found),'rejection_certificates':badcerts})
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':checks,'premises':premises,'records':records}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':status,'seconds':r['seconds'],'hashes':len(checks),'models':len(records),'tested':sum(x['tested'] for x in records),'positive':sum(x['positives'] for x in records),'rejections':sum(len(x['rejection_certificates']) for x in records)}))
