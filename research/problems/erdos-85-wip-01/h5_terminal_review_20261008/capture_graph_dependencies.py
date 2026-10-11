"""Read-only audit of H5's earlier graph-cover dependency build."""
import base64,hashlib,json,shlex,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
JOB='20261008T112554-erdos85__h5-formal-20261008-454084'
COMMIT='f7117ae8d261c6a0ad7176503983d6938532c1ae'
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
    graph=json.loads((ROOT/'graph-axioms.json').read_text())
    code='''from pathlib import Path
from datetime import datetime
import subprocess,hashlib,json,re,base64
def sha(data):return hashlib.sha256(data).hexdigest()
job=Path('/opt/e85/jobs')/CONFIG['job']
repo=Path('/opt/e85/wt/erdos85__h5-formal-20261008')
cache=Path('/var/lib/docker/volumes/lean-build-erdos85__h5-formal-20261008/_data/lib/lean/Proofs')
files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
raw=files['job.log'].decode();assert int(files['job.exit'])==0
assert re.findall(r'^\\[e85\\] commit ([a-f0-9]{40}) ',raw,re.M)==[CONFIG['commit']]
assert 'Build completed successfully (' in raw and '=== Build succeeded ===' in raw
assert not re.search(r'\\berror:',raw,re.I) and 'sorry' not in raw.lower()
start=datetime.fromisoformat(re.search(r'^\\[e85\\] job .* started (\\S+)',raw,re.M)[1].replace('Z','+00:00')).timestamp()
finish=(job/'exit').stat().st_mtime
def info(module):
 script='import pathlib,hashlib,json,sys;p=pathlib.Path(sys.argv[1]);s=p.stat();print(json.dumps({"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"bytes":s.st_size,"mtime":s.st_mtime}))'
 return json.loads(subprocess.check_output(['sudo','python3','-c',script,str(cache/(module+'.olean'))]))
modules=['Erdos85OrderFortyNineSmallHighLabelingBridge','Erdos85OrderFortyNineSmallHighFiberLabeling']+list(CONFIG['graph']['sources'])
rows=[]
for module in modules:
 path='proofs/Proofs/'+module+'.lean'
 source=subprocess.check_output(['git','-C',str(repo),'show',CONFIG['commit']+':'+path])
 assert source==subprocess.check_output(['git','-C',str(repo),'show',CONFIG['graph']['execution_commit']+':'+path])
 assert source==(repo/path).read_bytes()
 assert not re.search(r'\\b(sorry|unsafe|implemented_by)\\b',source.decode())
 assert not re.search(r'^\\s*(?:private\\s+)?axiom\\s',source.decode(),re.M)
 if module in CONFIG['graph']['sources']:assert sha(source)==CONFIG['graph']['sources'][module]['sha256']
 built=re.findall(r'\\] Built Proofs\\.'+re.escape(module)+r' \\(([^)]+)\\)',raw);assert len(built)==1
 obj=info(module);assert obj['bytes']>0 and start<=obj['mtime']<=finish
 files['sources/'+module+'.lean']=source
 rows.append({'module':module,'source_sha256':sha(source),'object':obj,'fresh_build_elapsed':built[0]})
for row in rows:assert info(row['module'])==row['object']
assert (job/'log').read_bytes()==files['job.log']
report={'status':'H5_GRAPH_DEPENDENCY_ARTIFACT_AUDIT_PASS','job':job.name,'execution_commit':CONFIG['commit'],
        'h5_execution_commit':CONFIG['graph']['execution_commit'],'authoritative_exit':0,'results':rows,
        'scope':'Five graph dependency objects only. Final H5 exported axiom sets and all search objects require their own terminal audit.',
        'retained_sha256':{n:sha(b) for n,b in files.items()}}
print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
'''
    config={'job':JOB,'commit':COMMIT,'graph':graph}
    remote='CONFIG='+repr(config)+'\n'+code
    result=subprocess.check_output(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(remote)])
    bundle=json.loads(result);audit=bundle['audit'];files={n:base64.b64decode(b) for n,b in bundle['files'].items()}
    for n,b in files.items():assert sha(b)==audit['retained_sha256'][n]
    files['collector.py']=Path(__file__).read_bytes();files['graph-input.json']=(ROOT/'graph-axioms.json').read_bytes()
    audit['retained_sha256']={n:sha(b) for n,b in files.items()};files['AUDIT.json']=(json.dumps(audit,indent=2)+'\n').encode()
    for n,b in files.items():
        path=ROOT/'graph-dependency-evidence1'/n;path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():assert path.read_bytes()==b,'Refusing evidence overwrite: '+n
        else:
            with path.open('xb') as f:f.write(b)
    print(audit['status']);print('Independently checked dependency objects:',len(audit['results']))
if __name__=='__main__':main()
