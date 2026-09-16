from pathlib import Path
import hashlib,json,time,collections
P=Path(__file__).parent;A=Path('/Users/rwalters/lean-genius-h1-cube25-run-provenance-sol1-20260916');S=Path('/Users/rwalters/lean-genius-cayley-sol2-20260915/h1-cube25-evidence')
read=lambda p:json.loads(p.read_text())
start=time.monotonic()
def digest(p):
 h=hashlib.sha256();before=p.stat()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(4194304),b''):
   assert time.monotonic()-start<120;h.update(block)
 after=p.stat();assert (before.st_size,before.st_mtime_ns,before.st_ino)==(after.st_size,after.st_mtime_ns,after.st_ino)
 return h.hexdigest(),before.st_size
for n,h in read(A/'pins.json').items():assert digest(A/n)[0]==h
r=read(A/'results.json');c=read(S/'candidate.json');launch=read(A/'launch.json')
for name,key in [('candidate.json','candidate_sha256'),('archive-scan.json','archive_scan_sha256')]:assert digest(S/name)[0]==launch[key]
assert digest(A/'audit.py')[0]==launch['driver_sha256']
expected={v['path']:v for v in read(S/'archive-scan.json')['root_verdicts'] if v['tag']=='0bbee37fe45d9447'};assert set(expected)=={v['path'] for v in r['verdicts']}
groups=collections.defaultdict(list);labels=collections.Counter()
for v in r['verdicts']:
 path=Path(v['path']);h,size=digest(path);assert h==v['sha256']==expected[str(path)]['sha256'] and size==v['bytes'];text=path.read_text();assert text==v['text']
 tokens=text.split();assert tokens[0]=='0bbee37fe45d9447' and tokens[1]=='UNSAT' and 'mode:CUBE25' in tokens
 assert json.loads(text.split('table:',1)[1])==c['table']
 label='VERIFIED_AGGREGATE_ONLY' if 'drat:VERIFIED' in tokens else 'NOT_VERIFIED_AGGREGATE';assert label==v['label'];labels[label]+=1;groups[h].append(str(path))
assert len(groups)==3 and labels=={'VERIFIED_AGGREGATE_ONLY':2,'NOT_VERIFIED_AGGREGATE':2}
assert dict(groups)==r['identical_verdict_locations'];assert r['selected_verdict_path']==c['verdict_path'] and r['selected_verdict_sha256']==c['verdict_sha256']
root=Path(r['selected_cube_directory']);assert root.parent==Path(c['verdict_path']).parent
assert sorted(x['cube'] for x in r['cubes'])==list(range(25));source={x['cube']:x for x in c['cubes']};total=0
for x in r['cubes']:
 i=x['cube'];inp=x['input'];proof=x['proof_gzip'];assert inp['path']==source[i]['path'] and inp['sha256']==source[i]['sha256']
 assert Path(inp['path'])==root/f'c{i}.cnf' and Path(proof['path'])==root/f'c{i}.drat.gz'
 for rec in [inp,proof]:assert digest(Path(rec['path']))==(rec['sha256'],rec['bytes'])
 total+=proof['bytes'];assert x['proof_verified'] is False
assert total==r['compressed_proof_bytes']==5583310051
assert r['same_directory_log_files']==[x.name for x in root.iterdir() if x.suffix in ['.log','.out','.err']]==[]
out={'status':'PASS_SELECTED_ARTIFACT_BYTES_AND_VERDICT_SEPARATION','verdict_locations':4,'distinct_contents':3,'cube_inputs':25,'compressed_proofs':25,'compressed_bytes':total,'seconds':time.monotonic()-start,'scope':'Names/hashes and aggregate verdict provenance only; no decompression, proof validity, category admission or exclusion.'}
(P/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
