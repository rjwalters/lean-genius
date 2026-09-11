from pathlib import Path
import json,itertools as it,time,hashlib,sqlite3
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');p=b/'residual-ten-D5-five-311-symmetry';o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
nh=0
for name in ['pins.json','input-pins.json']:
 if not (p/name).exists():continue
 for k,v in read(p/name).items():
  q=Path(k);q=q if q.is_absolute() else p/q
  assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2460,2463,2464,2467]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
d=read(p/'results.json');assert d['status']=='COMPLETE'
pack=read(b/'residual-ten-D5-five-311-packing/results.json')['records'];dom=read(b/'residual-ten-D5-supports/results.json')['records'];high=read(b/'residual-ten-D5-five-311-high-matchings/results.json')['records'];hm={r['root']:r for r in high};assert len(hm)==len(high)
start=time.monotonic();status='INCOMPLETE';seen=set();nmatch=0;counts=[]
def guard():
 if time.monotonic()-start>30:raise TimeoutError
def supports(ci,ri):
 out=[]
 for j in pack[ci]['survivors'][ri]['high3']:
  s=dom[ci]['high3'][j];out.extend([frozenset(s),frozenset(v^1 for v in s)])
 return out
try:
 for rec in d['records']:
  ci=rec['class'];E={frozenset(e) for e in dom[ci]['edges']};autos=set()
  for perm in it.permutations(range(5)):
   for bits in range(32):
    f=tuple(2*perm[v//2]+((v%2)^((bits>>(v//2))&1)) for v in range(10))
    if {frozenset(f[v] for v in e) for e in E}==E:autos.add(f)
  assert autos==set(map(tuple,rec['automorphisms'])) and len(autos)==len(rec['automorphisms'])
  for orbit in rec['orbits']:
   guard();rr=orbit['representative_root'];sr=orbit['representative_source_root'];S=supports(ci,sr);q=pack[ci]['survivors'][sr]['q'];assert hm[rr]['source_root']==sr
   for member in orbit['members']:
    guard();mr=member['root'];ms=member['source_root'];assert mr not in seen;seen.add(mr)
    assert hm[mr]['source_root']==ms and hm[mr]['class']==ci
    f=rec['automorphisms'][member['automorphism']];T=supports(ci,ms);lookup={s:i for i,s in enumerate(T)};assert len(lookup)==10
    g=[lookup[frozenset(f[v] for v in s)] for s in S];assert sorted(g)==list(range(10)) and all(g[v^1]==(g[v]^1) for v in range(10))
    tq=pack[ci]['survivors'][ms]['q'];assert all(tq[f[v]]==q[v] for v in range(10))
    maskmap={m:sum(1<<f[v] for v in range(10) if m&(1<<v)) for m in range(1024)}
    expected={}
    for h in hm[rr]['survivors']:
     edges=tuple(sorted(tuple(sorted((g[v],g[w]))) for v,w in h['edges']));rows=[None]*10
     for v,row in enumerate(h['Q_domains']):rows[g[v]]=tuple(sorted(maskmap[m] for m in row))
     assert edges not in expected;expected[edges]=tuple(rows)
    actual={tuple(sorted(tuple(sorted(e)) for e in h['edges'])):tuple(tuple(sorted(row)) for row in h['Q_domains']) for h in hm[mr]['survivors']}
    assert len(actual)==len(hm[mr]['survivors']) and actual==expected;nmatch+=len(actual)
  counts.append((ci,len(autos),len(rec['orbits'])))
 assert seen==set(hm) and nmatch==30256 and counts==[(5,64,32),(6,192,9),(7,3840,2)]
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':nh,'roots':len(seen),'matchings':nmatch,'classes':counts}
(o/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
