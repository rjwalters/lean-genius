import itertools as it,json,time,hashlib,sqlite3
from pathlib import Path
out=Path(__file__).parent;p=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-s4-character');read=lambda f:json.loads(f.read_text());start=time.monotonic();cap=30
ncheck=0
for f,root in [(p/'pins.json',p),(p/'input-pins.json',Path('/'))]:
 for name,h in read(f).items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h;ncheck+=1
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
states=[]
for id in (2207,2257,2315,2322,2357,2364):
 r=dict(con.execute('select * from review_requests where id=?',(id,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');states.append(r)
(out/'premise-states.json').write_text(json.dumps(states,indent=2)+'\n')
g=next(x for x in read(Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters/groups.json')) if x['name']=='S4')
P=list(it.permutations(range(4))); ix={x:i for i,x in enumerate(P)};M=[[ix[tuple(a[b[k]] for k in range(4))] for b in P] for a in P]
assert M==g['multiplication'] and [list(x) for x in P]==g['elements']
# At most3 generators suffice for any group of order<=8: each strict adjunction doubles size.
subs=set()
for size in range(4):
 for generators in it.combinations(range(1,24),size):
  H={0};todo=[0]
  for x in todo:
   for y in generators:
    z=M[x][y]
    if z not in H:H.add(z);todo.append(z)
   if len(H)>8:break
  if len(H)<=8:subs.add(frozenset(H))
  assert time.monotonic()-start<cap
assert len(subs)==28
# Classify directly by cycle lengths, independent of conjugation formula.
def typ(a):
 unseen=set(range(4));cycles=[]
 while unseen:
  x=min(unseen);y=x;k=0
  while y in unseen:unseen.remove(y);k+=1;y=a[y]
  cycles.append(k)
 return tuple(sorted(cycles))
r=read(p/'results.json');types=[typ(P[C[0]]) for C in r['classes']]
assert r['classes']==[[i for i,a in enumerate(P) if typ(a)==t] for t in types]
chars={}
for H in subs:
 cosets=set(frozenset(M[a][h] for h in H) for a in range(24))
 v=tuple(sum(frozenset(M[C[0]][a] for a in B)==B for B in cosets) for C in r['classes'])
 bounds=[78 if t==(1,1,1,1) else 3 if t==(1,3) else 6 for t in types]
 if all(x<=b for x,b in zip(v,bounds)):chars.setdefault(v,set()).add(H)
assert len(chars)==9
expected={tuple(c['values']):{frozenset(h) for h in c['subgroups']} for c in r['characters']}
assert chars==expected
vs=sorted(chars);sol=[];tested=0
for k in (7,8):
 for ids in it.combinations_with_replacement(range(len(vs)),k):
  tested+=1
  totals=tuple(sum(vs[j][i] for j in ids) for i in range(5))
  if totals[0]!=78:continue
  if all(x in ((0,3) if t==(1,3) else (0,2,4,6)) for t,x in zip(types[1:],totals[1:])):sol.append((ids,totals))
  assert time.monotonic()-start<cap
assert set(sol)=={(tuple(s['indices']),tuple(s['fixed_counts'])) for s in r['solutions']}
assert len(sol)==9 and len({tuple(vs[j][0] for j in ids) for ids,t in sol})==7
result={'status':'COMPLETE','original_cap_seconds':cap,'seconds':time.monotonic()-start,'verified_hashes':ncheck,'subgroups':len(subs),'characters':len(chars),'unpruned_multisets':tested,'solutions':len(sol),'patterns':sorted({tuple(vs[j][0] for j in ids) for ids,t in sol})}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
