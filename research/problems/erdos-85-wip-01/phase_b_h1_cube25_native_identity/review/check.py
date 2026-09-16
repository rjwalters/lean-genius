import hashlib,json,itertools,subprocess,time
from pathlib import Path
P=Path(__file__).parent;A=Path('/Users/rwalters/lean-genius-h1-cube25-native-identity-sol1-20260916');W=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration');R=W/'research/problems/erdos-85-wip-01'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic();pins=read(A/'pins.json');assert len(pins)==16
for n,h in pins.items():assert sha(A/n)==h,n
launch=read(A/'launch.json');receipt=read(A/'receipt.json');candidate=read(A/'candidate.json');manifest=R/'phase_b_h1_h3/h1-frozen-candidates.json';assert sha(manifest)==launch['manifest_sha256']==receipt['manifest_sha256']
row=next(r for r in read(manifest)['rows'] if r['id']==receipt['id']);pairs=[p for p in itertools.combinations(range(8),2) if p[1]!=(p[0]^1)];table=[[list(p),v] for p,v in zip(pairs,row['table_values'],strict=True) if v]
assert table==candidate['table']==read(A/'native/table.json');assert hashlib.sha1(json.dumps(table).encode()).hexdigest()[:16]==row['tag']=='0bbee37fe45d9447'
assert int(row['profile'])==receipt['profile']==0 and sha(A/'native/table.json')==receipt['table_sha256']
basepath=Path(receipt['cnf_path']);raw=basepath.read_bytes();assert hashlib.sha256(raw).hexdigest()==receipt['cnf_sha256'] and len(raw)==receipt['cnf_bytes']
lines=raw.splitlines(keepends=True);assert lines[0]==b'p cnf 42188 613280\n' and len(lines)==613281
for line in lines[1:]:
 values=list(map(int,line.split()));assert values and values[-1]==0 and all(0<abs(v)<=42188 for v in values[:-1])
body=b''.join(lines[1:]);seen=set()
for c in candidate['cubes']:
 assert time.monotonic()-start<60
 data=Path(c['path']).read_bytes();assert hashlib.sha256(data).hexdigest()==c['sha256'] and len(data)==c['bytes']
 parts=data.splitlines(keepends=True);assert parts[0]==b'p cnf 42188 613282\n';assert b''.join(parts[1:-2])==body
 units=tuple(int(x.split()[0]) for x in parts[-2:]);assert units==tuple(c['units']) and units not in seen;seen.add(units)
 assert parts[-2:]==[f'{u} 0\n'.encode() for u in units]
assert len(candidate['cubes'])==25 and seen==set(itertools.product(range(301,306),range(456,461)))
for name,key in [('materialize_h1_verdict_input.py','runner_sha256'),('materialize_verdict_input.py','validator_sha256')]:assert sha(A/'source'/name)==launch[key]==receipt[key]==sha(R/'sat49'/name)
for phase in ['emit','check']:
 rec=receipt[phase];assert rec['returncode']==0 and rec['seconds']<120 and '--network' in rec['command'] and 'none' in rec['command']
assert (A/'native/check.log').read_text()=='MATCH (613280 clauses, top 42188)\n'
assert read(A/'generation.json')['seconds']<300 and receipt['container_absent']
cmd=receipt['emit']['command'];docker=cmd[0];name=cmd[cmd.index('--name')+1]
assert not subprocess.check_output([docker,'ps','-aq','--filter','name='+name],timeout=15).strip()
image=subprocess.check_output([docker,'image','inspect',receipt['image_id'],'--format','{{.Id}}'],timeout=15).decode().strip();assert image==receipt['image_id']==launch['image_id']
mount=next(x for x in cmd if 'dst=/v2cnf' in x);emitter=Path(mount.split('src=')[1].split(',dst=')[0]);assert sha(emitter)==receipt['emitter_sha256']==launch['emitter_sha256']
loc=read(A/'artifact-locations.json')['files']['input.cnf'];assert loc=={'path':str(basepath),'sha256':receipt['cnf_sha256'],'bytes':len(raw)}
result={'status':'PASS_FRESH_IDENTITY_AND25_EXACT_CUBE_JOINS','author_payloads':16,'cube_count':25,'base_sha256':receipt['cnf_sha256'],'variables':42188,'clauses':613280,'bytes':len(raw),'container_absent_now':True,'image_and_emitter_identity_checked':True,'seconds':time.monotonic()-start,'scope':'Read-only identity/provenance audit; native generation not repeated, no proof verification or exclusion.'}
(P/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
