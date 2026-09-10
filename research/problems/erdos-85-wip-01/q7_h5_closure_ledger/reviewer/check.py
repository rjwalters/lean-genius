from pathlib import Path
import json,itertools,hashlib,sqlite3,collections,re
p=Path(__file__).parent;s=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h5-closure-ledger');root=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration')
def load(f):return json.loads((s/f).read_text())
pins=load('pins.json');assert all(hashlib.sha256((s/f).read_bytes()).hexdigest()==h for f,h in pins.items())
up=load('source-pins.json');assert len(up)==136 and all(hashlib.sha256((root/f).read_bytes()).hexdigest()==h for f,h in up.items())
for f,origin in load('origins.json').items():assert (s/f).read_bytes()==(root/origin['path']).read_bytes() and hashlib.sha256((s/f).read_bytes()).hexdigest()==origin['sha256']
# Enumerate packings of the ten high pairs by recursive disjoint triangle edge sets.
triples=list(itertools.combinations(range(5),3));tri_edges=[set(itertools.combinations(t,2)) for t in triples];systems=[]
def pack(start,used,chosen):
 systems.append(tuple(chosen))
 for i in range(start,10):
  if not used&tri_edges[i]:pack(i+1,used|tri_edges[i],chosen+[i])
pack(0,set(),[])
assert collections.Counter(map(len,systems))=={0:1,1:10,2:15}
for sys in systems:
 sets=[set(triples[i]) for i in sys]
 if not sets:continue
 if len(sets)==1:order=sorted(sets[0])+sorted(set(range(5))-sets[0])
 else:
  a,b=sets;inter=a&b;assert len(inter)==1;order=list(inter)+sorted(a-b)+sorted(b-a)
 perm={c:i for i,c in enumerate(order)}
 normalized=sorted(sum(1<<perm[c] for c in t) for t in sets)
 assert normalized==([7] if len(sets)==1 else [7,25])
lean=(s/'canonical-masks.lean').read_text();family=[]
for t,ts in enumerate([[],[{0,1,2}],[{0,1,2},{0,3,4}]]):
 heavy=[sum(1<<c for c in x) for x in ts]+[sum(1<<c for c in pair) for pair in itertools.combinations(range(5),2) if not any(set(pair)<=x for x in ts)]
 multiplicities=[8-sum(bool(m>>c&1) for m in heavy) for c in range(5)]
 assert multiplicities==[4+sum(c in x for x in ts) for c in range(5)]
 masks=[0]*5+heavy+sum(([1<<c]*multiplicities[c] for c in range(5)),[])+[0]*(14-t)
 block=lean.split('def orderFortyNineFiveHighT'+str(t)+'Masks',1)[1].split('#[',1)[1].split(']',1)[0]
 actual=[int(x.strip()) for x in block.replace('\n',' ').split(',') if x.strip()]
 assert masks==actual and len(masks)==49
 assert all(sum(bool(m>>c&1) for m in masks)==8 for c in range(5))
 assert all(sum((m>>a&1) and (m>>b&1) for m in masks)==1 for a,b in itertools.combinations(range(5),2))
 core=load('core-t'+str(t)+'.json');assert core['masks']==heavy and core['complete'] and core['stop'] is None and len(set(core['canonical_cores']))==[1665,249,13][t]
 family.append(dict(t=t,support_counts=[sum(m.bit_count()==k for m in masks[5:]) for k in range(4)],heavy_cores=len(core['canonical_cores'])))
conn=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);conn.row_factory=sqlite3.Row
reviews=load('reviews.json');assert {r['id'] for r in reviews}=={2022,2032,2037,2062,2063}
for r in reviews:
 live=dict(conn.execute('SELECT * FROM review_requests WHERE id=?',(r['id'],)).fetchone())
 assert r['status']==live['status']=='resolved' and r['resolution']==live['resolution'] and r['resolution'].startswith('PASS')
t0=load('t0-chain.json');assert [t0[k] for k in ['core_count','host_positive','singleton_positive','empty_excluded']]==[1665,761,14,13] and t0['uncovered_domain']==[]
assert t0['preserved_search_unknown']==[t0['independent_counting_argument_core']]==[5774048758818]
t1=load('t1-chain.json');assert t1['chain']['heavy_domain']==249 and t1['chain']['joint_feasible']==211 and t1['chain']['singleton_exhausted']==201 and t1['independent_empty_cores']==10 and t1['remaining_cores']==0
t2=load('t2-chain.json');left=set(load('core-t2.json')['canonical_cores'])
for r in t2['stages']:
 assert sorted(left)==r['before'] and set(r['excluded'])<=left;left-=set(r['excluded']);assert sorted(left)==r['after']
assert left=={44} and t2['remaining']==[44]
c=load('core44-chain.json');rows=c['rows'];assert len(rows)==len({json.dumps(r['key']) for r in rows})==92
assert collections.Counter(r['key'][0] for r in rows)=={0:16,1:40,2:36}
assert collections.Counter(r['review'] for r in rows)=={2049:64,2050:1,2051:5,2055:8,2056:4,2058:5,2059:1,2061:4}
assert [r['key'] for r in rows if r['review']==2050]==[[1,11,[],4,2]]
assert [r['key'] for r in rows if r['review']==2059]==[[1,7,[],4,2]]
assert c['uncovered']==c['multiply_assigned']==0
cover=(s/'canonical-cover.lean').read_text();sig=cover.split('theorem orderFortyNineStratumExcluded_five_of_booleanExclusions',1)[1].split(':=',1)[0]
for i in range(3):assert '(h'+str(i)+' : ∀ edges : BitVec 1176' in sig and 'orderFortyNineFiveHighT'+str(i)+'Masks' in sig
out=dict(status='PASS',triple_packings=len(systems),normal_forms=3,families=family,upstream_hashes_verified=len(up),local_pins_verified=len(pins),review_snapshots_verified=[r['id'] for r in reviews],scope='Outer H5 mathematical/finite-computation closure under accepted reduction/exclusion reviews; no Lean Boolean premises discharged, no queue/global result.')
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
