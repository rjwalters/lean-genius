from pathlib import Path
import json,itertools as it,time,hashlib,sqlite3
p=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-order-twelve-final-composition');root=p.parent;out=Path(__file__).parent;read=lambda p:json.loads(p.read_bytes());seen=set();hashes={}
def pins(f):
 f=f.resolve()
 if f in seen:return
 seen.add(f);hashes[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest()
 for n,h in read(f).items():
  q=(f.parent/n).resolve();actual=hashlib.sha256(q.read_bytes()).hexdigest();assert actual==h,(str(q),actual,h);hashes[str(q)]=actual
  if q.name in ('pins.json','input-pins.json'):pins(q)
pins(p/'pins.json');case=read(p/'case-map.json');prior=read(p/'result.json');db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);states={}
# Independently specified complete terminal/cover set, including transitive scope checks.
ids=[2487,2489,2494,2555,2544,2627,2496,2491,2597,2602,2498,2516,2520,2501,2521,2522,2524,2528,2606,2553]
for id in ids+[2512,2599,2600,2601]:
 s,b,n,refs=db.execute('select status,body,resolution,refs from review_requests where id=?',(id,)).fetchone();assert s=='resolved' and (n.startswith('SCOPED PASS') if id==2599 else n.startswith('PASS'));states[id]=dict(status=s,body=b,resolution=n,refs=json.loads(refs))
 for ref in json.loads(refs):pins(Path(ref))
assert set(prior['direct_roots'])==set(ids)
for f,h in prior['verified_hashes'].items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
errpath=root/'n78-a4-four-orbit-attachment-cover/ERRATUM.json';err=read(errpath)
for n,h in err['unchanged_payload_hashes'].items():assert hashlib.sha256((errpath.parent/n).read_bytes()).hexdigest()==h
assert err['saved_local_rows_checked_against_actual_Q']==1044
assert Path('/tmp/erdos85-sol1-review2602/ERRATUM.md').is_file()
start=time.monotonic();profiles=[]
# Bound only by the full vertex budget, then impose the reviewed fixed marks.
for a in range(27):
 for b in range((78-3*a)//6+1):
  for c in range((78-3*a-6*b)//4+1):
   rest=78-3*a-6*b-4*c
   if rest%12==0 and 3*a+2*b in (2,6) and c in (0,3):profiles.append((a,b,c,rest//12))
assert sorted(profiles)==sorted(tuple(r['profile']) for r in case['groups']['A4']) and len(profiles)==6
expected={(2,0,0,6):[[2496]],(2,0,3,5):[[2491]],(0,3,0,5):[[2597]],(0,3,3,4):[[2602]],(0,1,3,5):[[2498],[2516],[2520]],(0,1,0,6):[[2501],[2524],[2528],[2606]]}
for r in case['groups']['A4']:assert [b['reviews'] for b in r['branches']]==expected[tuple(r['profile'])]
assert case['group_cover']==[2489,2494] and case['prior_order_bound']==2487
assert {k:v for k,v in case['groups'].items() if k!='A4'}==dict(C12=[2555],Dic12=[2555],C3xV4=[2544],S3xC2=[2627])
# Exceptional B12 degree multiset22111: exactly WW, WY, YY placements.
placements={tuple(sorted('W' if i<2 else 'Y' for i in chosen)) for chosen in it.combinations(range(5),2)};assert placements=={('W','W'),('W','Y'),('Y','Y')}
remaining=[n for n in [1,2,3,4,6,8,12] if n!=12];assert case['conditional_conclusion']==dict(excluded_order=12,remaining_orders=remaining)
r=dict(status='PASS_FULL_AUT_ORDER_TWELVE_EXCLUSION',fresh_review_count=len(states),distinct_verified_files=len(hashes),A4_profiles=sorted(profiles),remaining_full_orders=remaining,full_order_bound=8,seconds=time.monotonic()-start,original_cap_seconds=30,loading_hashing_outside_clock=True,scope='Full automorphism group only; N78/N80 existence/global/Lean unresolved')
(out/'result.json').write_text(json.dumps(r,indent=2)+'\n');(out/'review-states.json').write_text(json.dumps(states,indent=2)+'\n');(out/'verified-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n');print(r)
