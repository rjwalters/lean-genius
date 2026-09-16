"""Pin retained run artifacts; hashing is not proof verification."""
import hashlib,json,time
from pathlib import Path
P=Path(__file__).parent;S=Path('/Users/rwalters/lean-genius-cayley-sol2-20260915/h1-cube25-evidence')
read=lambda p:json.loads(p.read_text());digest=lambda b:hashlib.sha256(b).hexdigest()
c=read(S/'candidate.json');scan=read(S/'archive-scan.json');root=Path(c['cubes'][0]['path']).parent
assert not (P/'launch.json').exists()
(P/'launch.json').write_text(json.dumps({'seconds':120,'proof_files':25,'compressed_proof_bytes':5583310051,'candidate_sha256':digest((S/'candidate.json').read_bytes()),'archive_scan_sha256':digest((S/'archive-scan.json').read_bytes()),'driver_sha256':digest(Path(__file__).read_bytes()),'scope':'Read-only hashes only. No decompression, proof checker or solver.'},indent=2)+'\n');start=time.monotonic()
verdicts=[];groups={}
for v in scan['root_verdicts']:
 if v['tag']!=c['id'].removeprefix('h1_'):continue
 p=Path(v['path']);raw=p.read_bytes();assert digest(raw)==v['sha256'] and raw.decode()==v['text'];tokens=raw.decode().split();label='VERIFIED_AGGREGATE_ONLY' if 'drat:VERIFIED' in tokens else 'NOT_VERIFIED_AGGREGATE'
 assert 'mode:CUBE25' in tokens and json.loads(raw.decode().split('table:',1)[1])==c['table']
 row={'path':str(p),'sha256':digest(raw),'bytes':len(raw),'label':label,'text':raw.decode()};verdicts.append(row);groups.setdefault(digest(raw),[]).append(str(p))
assert len(verdicts)==4 and len(groups)==3 and sum(v['label']=='VERIFIED_AGGREGATE_ONLY' for v in verdicts)==2
assert any(v['path']==c['verdict_path'] and v['sha256']==c['verdict_sha256'] for v in verdicts)
rows=[]
for cube in c['cubes']:
 assert time.monotonic()-start<120
 i=cube['cube'];inp=Path(cube['path']);raw=inp.read_bytes();assert digest(raw)==cube['sha256'] and len(raw)==cube['bytes']
 proof=root/f'c{i}.drat.gz';before=proof.stat();h=hashlib.sha256()
 with proof.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):
   assert time.monotonic()-start<120;h.update(block)
 after=proof.stat();assert (before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_ino,after.st_size,after.st_mtime_ns)
 core=root/f'c{i}.core.cnf';assert core.exists()
 rows.append({'cube':i,'input':{'path':str(inp),'sha256':cube['sha256'],'bytes':len(raw)},'proof_gzip':{'path':str(proof),'sha256':h.hexdigest(),'bytes':before.st_size},'core_observation':{'path':str(core),'bytes':core.stat().st_size},'proof_verified':False})
assert len(rows)==25 and sum(x['proof_gzip']['bytes'] for x in rows)==5583310051
out={'status':'PASS_ARTIFACT_PROVENANCE_ONLY','case_id':c['id'],'selected_verdict_path':c['verdict_path'],'selected_verdict_sha256':c['verdict_sha256'],'selected_cube_directory':str(root),'verdicts':verdicts,'distinct_verdict_contents':len(groups),'identical_verdict_locations':groups,'cubes':rows,'compressed_proof_bytes':5583310051,'same_directory_log_files':[x.name for x in root.iterdir() if x.suffix in ['.log','.out','.err']],'seconds':time.monotonic()-start,'scope':'Selected run filenames/input hashes and retained compressed proof bytes are pinned. Aggregate VERIFIED is historical metadata only. NOT-VERIFIED siblings remain separate; no per-cube verification or category admission.'}
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['verdicts','identical_verdict_locations','cubes']})
