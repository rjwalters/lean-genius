"""Exact byte comparison of all archived cube inputs with the fresh canonical base."""
import hashlib,itertools,json,time
from pathlib import Path
P=Path(__file__).parent;C=Path('/Users/rwalters/lean-genius-cayley-sol2-20260915/h1-cube25-evidence/candidate.json')
read=lambda p:json.loads(p.read_text());digest=lambda b:hashlib.sha256(b).hexdigest()
assert not (P/'comparison-launch.json').exists()
c=read(C);r=read(P/'receipt.json');native=Path(r['cnf_path']);base=native.read_bytes();assert digest(base)==r['cnf_sha256'] and len(base)==r['cnf_bytes']
header,body=base.split(b'\n',1);fields=header.split();assert fields==[b'p',b'cnf',b'42188',b'613280'];assert body.endswith(b' 0\n') or body.endswith(b'0\n')
expected_header=b'p cnf 42188 613282\n';start=time.monotonic()
(P/'comparison-launch.json').write_text(json.dumps({'seconds':60,'cases':25,'candidate_sha256':digest(C.read_bytes()),'native_sha256':digest(base),'driver_sha256':digest(Path(__file__).read_bytes()),'scope':'Read-only exact bytes, no proof replay.'},indent=2)+'\n')
seen=set();rows=[]
for row in c['cubes']:
 assert time.monotonic()-start<60
 units=tuple(row['units']);assert units not in seen and units in set(itertools.product(range(301,306),range(456,461)));seen.add(units)
 path=Path(row['path']);raw=path.read_bytes();assert digest(raw)==row['sha256'] and len(raw)==row['bytes']
 expected=expected_header+body+f'{units[0]} 0\n{units[1]} 0\n'.encode()
 assert raw==expected,('cube byte difference',row['cube'])
 assert digest(path.read_bytes())==row['sha256']
 rows.append({'cube':row['cube'],'path':str(path),'sha256':digest(raw),'bytes':len(raw),'units':list(units),'byte_equal_to_fresh_base_plus_units':True})
assert seen==set(itertools.product(range(301,306),range(456,461))) and len(rows)==25
assert digest(native.read_bytes())==r['cnf_sha256']
out={'status':'PASS_ALL25_EXACT_FRESH_NATIVE_CUBE_BYTES','case_id':c['id'],'native_path':str(native),'base_sha256':r['cnf_sha256'],'base_bytes':len(base),'cube_variables':42188,'cube_clauses':613282,'rows':rows,'seconds':time.monotonic()-start,'scope':'Discharges fresh canonical input identity gap only. Neither proof verification, CNF cover soundness, historical evidence admission nor exclusion is claimed.'}
(P/'comparison.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='rows'})
