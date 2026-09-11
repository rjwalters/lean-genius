from pathlib import Path
import json,hashlib,itertools
p=Path(__file__).resolve().parent
source=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-automorphism-at-most-sixteen');checked={}
def pins(f):
 for n,h in json.loads(f.read_text()).items():
  q=Path(n);q=q if q.is_absolute() else f.parent/q
  actual=hashlib.sha256(q.read_bytes()).hexdigest();assert actual==h,str(q);checked[str(q)]=h
pins(source/'pins.json');pins(source/'input-pins.json')
for n in json.loads((source/'input-pins.json').read_text()):pins(Path(n))
rs=json.loads((p/'premises.json').read_text());assert len(rs)==7 and all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in rs)
a=json.loads(Path('/tmp/erdos85-sol1-q9-n78-s4-sur-domain/results.json').read_text());b=json.loads(Path('/tmp/erdos85-sol1-q9-n78-s4-residual-neighborhoods/results.json').read_text());c=json.loads(Path('/tmp/erdos85-sol1-q9-n78-s4-residual-neighborhoods/certificates.json').read_text())
assert a['status']==b['status']=='COMPLETE'
roots=[(r['matching'],r['solution'],i) for r in a['records'] for i,_ in enumerate(r['survivors'])]
key=lambda r:(r['matching'],r['solution'],r['extension'])
assert len(roots)==len(set(roots))==576 and set(roots)==set(map(key,b['records']))==set(map(key,c))
assert len(b['records'])==len(c)==576 and all(r['excluded'] for r in b['records'])
for r in c:
 assert len(r['eligible'])==6
 assert {tuple(x['choice']) for x in r['all_subset_conflicts']}==set(itertools.combinations(r['eligible'],5))
remaining=[n for n in range(1,49) if 48%n==0 and n not in (24,48)]
assert remaining==[1,2,3,4,6,8,12,16]
out={'status':'PASS','checked_files':checked,'covered_roots':576,'certified_subsets':sum(len(r['all_subset_conflicts']) for r in c),'remaining_orders':remaining,'scope':'Full automorphism order at most16; graph existence unresolved.'}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'PASS','hashes':len(checked),'roots':576,'orders':remaining}))
