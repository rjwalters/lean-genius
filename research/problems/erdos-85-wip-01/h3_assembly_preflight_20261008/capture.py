"""Read-only independent capture of a pinned conditional assembly job."""
import argparse,base64,hashlib,json,re,shlex,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
CLOUD=r'''
import pathlib,hashlib,json,subprocess,base64,re
from datetime import datetime
def sha(b):return hashlib.sha256(b).hexdigest()
repo=pathlib.Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
area='research/problems/erdos-85-wip-01/h3_assembly_preflight_20261008'
root=repo/area;attempt=root/'attempt1';job=pathlib.Path('/opt/e85/jobs')/CONFIG['job']
if not (job/'exit').exists():
 pid=int((job/'pid').read_text());print(json.dumps({'status':'PENDING','pid':pid,'pid_live':pathlib.Path(f'/proc/{pid}').exists()}));raise SystemExit(0)
files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
assert re.findall(r'^\[e85\] commit ([a-f0-9]{40}) ',files['job.log'].decode(),re.M)==[CONFIG['commit']]
for name in ('H3AssemblyPreflight.lean','SOURCE.json','run.py'):
 data=subprocess.check_output(['git','-C',str(repo),'show',CONFIG['commit']+':'+area+'/'+name]);assert data==(root/name).read_bytes();files[name]=data
spec=json.loads(files['SOURCE.json']);source=files['H3AssemblyPreflight.lean'].decode()
assert sha(files['H3AssemblyPreflight.lean'])==spec['preflight_source_sha256']
assert 'native_decide' not in source and 'sorry' not in source
assert not re.search(r'^\s*axiom\s',source,re.M)
assert source.count(': triplePart 384 ')==3*384
assert [(int(a),int(b)) for a,b in re.findall(r'^  \| (\d+), _ => triplePart_384_(\d+)$',source,re.M)]==[(r,r) for r in range(384)]
cell=(repo/'research/problems/erdos-85-wip-01/h3_native_parts_20261008/source-review/Proofs/Erdos85H3TripleCompletionCell.lean').read_bytes()
assert sha(cell)==spec['production_cell_sha256']
files['RUN.json']=(attempt/'RUN.json').read_bytes();run=json.loads(files['RUN.json'])
files['compile.log']=(attempt/'compile.log').read_bytes()
assert sha(files['compile.log'])==run['log_sha256']
assert run['source_sha256']==spec['preflight_source_sha256']
assert run['cgroup_memory_bytes']==16*1024**3
quota,period=map(int,run['cgroup_cpu_max'].split());assert quota==period*2
for line in ('MEM_GB=16','TIMEOUT=3m','THREADS=1','CPUS=2','FULL=1'):assert line in files['job.spec'].decode().splitlines()
assert run['command']==['lean','-j1','H3AssemblyPreflight.lean','-o','/workspace/'+area+'/attempt1/H3AssemblyPreflight.olean']
assert run['timeout_seconds']==90 and not (repo/'proofs/H3AssemblyPreflight.lean').exists()
prior=repo/'research/problems/erdos-85-wip-01/h3_phase3_runtime_20261008/build-evidence/AUDIT.json'
files['prerequisite-AUDIT.json']=prior.read_bytes();assert sha(prior.read_bytes())==run['prerequisite_audit_sha256']
audit=json.loads(prior.read_text());assert audit['execution_commit']==spec['math_commit']
cache=pathlib.Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs')
for row in audit['results']:
 path='proofs/Proofs/'+row['module']+'.lean';data=(repo/path).read_bytes()
 assert sha(data)==row['source_sha256']
 assert data==subprocess.check_output(['git','-C',str(repo),'show',CONFIG['commit']+':'+path])
 assert subprocess.check_output(['sudo','sha256sum',str(cache/(row['module']+'.olean'))],text=True).split()[0]==row['olean_sha256']
rc=int(files['job.exit']);exports=[]
if rc==0:
 assert run['returncode']==0 and not run['timed_out'] and run['status']=='COMPILED_PENDING_AUDIT'
 raw=files['compile.log'].decode();assert not re.search(r'\b(sorry|error)\b',raw,re.I)
 found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)
 names=['Erdos85.H3TripleCompletion.AssemblyPreflight.'+n for n in ('threeHighCanonicalRepresentativeExcluded_one','orderFortyNineTripleCellExcluded_three_one')]
 assert [n for n,_ in found]==names
 for name,axioms in found:
  ax=[a.strip() for a in axioms.split(',') if a.strip()];assert set(ax)<={'propext','Quot.sound','Classical.choice'}
  exports.append({'theorem':name,'axioms':ax,'explicit_native_premises':384})
 obj=attempt/'H3AssemblyPreflight.olean';data=obj.read_bytes()
 assert sha(data)==run['object_sha256'] and len(data)==run['object_bytes']>0
 assert obj.stat().st_mtime==run['object_mtime']
 assert datetime.fromisoformat(run['started_utc']).timestamp()<=obj.stat().st_mtime<=(job/'exit').stat().st_mtime
else:assert run['returncode']!=0
report={'status':'CONDITIONAL_ASSEMBLY_AUDIT_PASS' if rc==0 else 'PREFLIGHT_FAILED','job':job.name,'execution_commit':CONFIG['commit'],'authoritative_exit':rc,'exports':exports,'run':run,'retained_sha256':{n:sha(b) for n,b in files.items()},'scope':'Conditional assembly only. No native result or whole-cell exclusion verified.'}
assert files['job.log']==(job/'log').read_bytes()
print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
'''
def main():
 p=argparse.ArgumentParser();p.add_argument('--job',required=True);p.add_argument('--commit',required=True);a=p.parse_args()
 assert re.fullmatch(r'\d{8}T\d{6}-erdos85__h3-triple-formal-20261007-\d+',a.job)
 assert re.fullmatch(r'[a-f0-9]{40}',a.commit)
 code='CONFIG='+repr(vars(a))+'\n'+CLOUD
 remote='import base64;exec(compile(base64.b64decode('+repr(base64.b64encode(code.encode()).decode())+'),"audit","exec"))'
 r=subprocess.run(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(remote)],capture_output=True)
 if r.returncode:print(r.stderr.decode());raise SystemExit(r.returncode)
 bundle=json.loads(r.stdout)
 if bundle.get('status')=='PENDING':print(json.dumps(bundle));return
 audit=bundle['audit'];audit['collector_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
 files={n:base64.b64decode(b) for n,b in bundle['files'].items()}
 for n,b in files.items():assert hashlib.sha256(b).hexdigest()==audit['retained_sha256'][n]
 files['AUDIT.json']=(json.dumps(audit,indent=2)+'\n').encode()
 for n,b in files.items():
  out=ROOT/'evidence1'/n;out.parent.mkdir(parents=True,exist_ok=True)
  if out.exists():assert out.read_bytes()==b
  else:out.write_bytes(b)
 print(audit['status']);print(json.dumps(audit['exports'],indent=2))
if __name__=='__main__':main()
