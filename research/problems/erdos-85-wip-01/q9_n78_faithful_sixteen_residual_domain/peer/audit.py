from pathlib import Path
import itertools as I,json,time,hashlib,sqlite3
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-n78-faithful-sixteen-residual-domain');expected=json.loads((src/'results.json').read_text());start=time.monotonic();cap=30
els=list(I.product(range(2),range(4),range(2)))
# Independent faithful permutations on matching S6.
perms=[tuple([z,1^z]+[2+(r+(-1 if s else 1)*v)%4 for v in range(4)]) for z,r,s in els]
ix={x:i for i,x in enumerate(perms)}
compose=lambda a,b:tuple(a[b[i]] for i in range(6))
M=[[ix[compose(a,b)] for b in perms] for a in perms];assert M==expected['multiplication']
inv=[next(j for j in range(16) if M[i][j]==0) for i in range(16)];assert inv==expected['inverse']
conn=[d for d in I.combinations(range(1,16),2) if all(inv[x] in d for x in d)];assert conn==[tuple(x) for x in expected['connections']];assert len(conn)==57

def pairings(vs):
 if not vs:yield ();return
 a=vs[0]
 for b in vs[1:]:
  for rest in pairings([v for v in vs if v not in (a,b)]):yield tuple(sorted(((a,b),)+rest))
def clean(N):
 seen=set()
 for row in N:
  for pair in I.combinations(sorted(row),2):
   if pair in seen:return False
   seen.add(pair)
 return True
out=[]
for rr in expected['records']:
 K={0,els.index((1,rr['reflection'],1))};cosets=sorted({tuple(sorted(M[g][h] for h in K)) for g in range(16)});assert cosets==[tuple(x) for x in rr['cosets']]
 label={g:i for i,c in enumerate(cosets) for g in c};moves=[[label[M[g][c[0]]] for c in cosets] for g in range(16)];assert moves==rr['moves']
 matches=[]
 for E in pairings(list(range(8))):
  if all({tuple(sorted((mp[a],mp[b]))) for a,b in E}==set(E) for mp in moves):matches.append(E)
 assert set(matches)=={tuple(tuple(e) for e in x) for x in rr['matchings']}
 matchindices={tuple(tuple(e) for e in x):i for i,x in enumerate(rr['matchings'])}
 saved={(s['matching'],s['connection'],s['origin']):tuple(tuple(e) for e in s['edges']) for s in rr['survivors']};found={};tested=0
 for E in matches:
  for di,D in enumerate(conn):
   for origin in range(8):
    if time.monotonic()-start>cap:raise TimeoutError
    edges=set(E)
    # Translate the identity's Y neighbors and cross edge by the independently verified action.
    for g in range(16):
     edges.add(tuple(sorted((8+g,moves[g][origin]))))
     for d in D:edges.add(tuple(sorted((8+g,8+M[g][d]))))
    N=[set() for _ in range(24)]
    for a,b in edges:N[a].add(b);N[b].add(a)
    assert all(len(row)==3 for row in N);tested+=1
    if clean(N):found[matchindices[E],di,origin]=tuple(sorted(edges))
 assert found==saved and tested==rr['tested'];out.append({'reflection':rr['reflection'],'matchings':len(matches),'tested':tested,'survivors':len(found)})
checks={}
for manifest in [src/'pins.json',src/'input-pins.json']:
 for name,h in json.loads(manifest.read_text()).items():
  f=Path(name) if Path(name).is_absolute() else manifest.parent/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;checks[str(f)]=h
c=sqlite3.connect('/Users/rwalters/GitHub/lean-genius/.squad/squad.db');c.row_factory=sqlite3.Row
states=[dict(c.execute('select * from review_requests where id=?',(i,)).fetchone()) for i in [2422,2425]];assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in states)
r={'status':'COMPLETE','cap_seconds':cap,'seconds':time.monotonic()-start,'records':out,'inverse_closed_pairs':len(conn),'all_pairs':105,'hashes':checks,'premises':states}
(p/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ('hashes','premises')}))
