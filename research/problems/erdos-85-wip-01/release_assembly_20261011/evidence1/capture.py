"""Read-only terminal capture of the bounded cloud endpoint validation."""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent
AREA = "research/problems/erdos-85-wip-01/release_assembly_20261011"
REMOTE = "/opt/e85/wt/erdos85__release-assembly-20261011"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--job", required=True)
    parser.add_argument("--commit", required=True)
    args = parser.parse_args()
    assert re.fullmatch(r"[a-f0-9]{40}", args.commit)
    assert re.fullmatch(r"[0-9]{8}T[0-9]{6}-erdos85__release-assembly-20261011-[0-9]+", args.job)
    code = '''
import base64,hashlib,json,re,subprocess
from pathlib import Path
repo=Path(REPO);root=repo/AREA;job=Path('/opt/e85/jobs')/JOB
if not (job/'exit').exists():
 print(json.dumps({'status':'PENDING'}));raise SystemExit(0)
assert (job/'exit').read_text().strip()=='0', (job/'log').read_text()[-8000:]
assert not Path('/proc/'+(job/'pid').read_text().strip()).exists()
assert (job/'sha').read_text().strip()==COMMIT
assert subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()==COMMIT
spec=(job/'spec').read_text().splitlines()
for line in ['MEM_GB=16','THREADS=1','CPUS=2','FULL=1','TIMEOUT=4m','VOLUME=lean-build-erdos85__h3-triple-formal-20261007']:
 assert line in spec,line
files={'job.'+n:(job/n).read_bytes() for n in ['log','spec','exit','sha']}
for name in ['validate.py','source-manifest.json']:
 b=(root/name).read_bytes()
 assert b==subprocess.check_output(['git','-C',str(repo),'show',COMMIT+':'+AREA+'/'+name])
 files[name]=b
out=root/'run-output-2';files['validation.json']=(out/'validation.json').read_bytes()
report=json.loads(files['validation.json']);manifest=json.loads(files['source-manifest.json'])
assert report['status']=='CONDITIONAL_RELEASE_ENDPOINTS_VALIDATED'
assert report['sources']==manifest['sources']
assert len(report['sources'])==893 and len(report['imported_objects'])==891
for name,digest in report['sources'].items():
 assert hashlib.sha256((repo/'proofs/Proofs'/(name+'.lean')).read_bytes()).hexdigest()==digest
plan=json.loads((root.parent/'order49_h3_closed_capstone_20261008/PLAN.json').read_text())
assert report['imported_objects']=={n:{k:v[k] for k in ['sha256','bytes']} for n,v in plan['objects'].items()}
assert report['memory_bytes']==16*1024**3
quota,period=map(int,report['cpu_max'].split());assert quota==2*period
assert [r['module'] for r in report['runs']]==['Erdos85OrderFortyNineCapstoneH3','Erdos85FiniteDropCapstone']
for run in report['runs']:
 name=run['module'];b=(out/(name+'.log')).read_bytes();files[name+'.log']=b
 assert hashlib.sha256(b).hexdigest()==run['log_sha256'] and run['returncode']==0
 assert run['elapsed_seconds']<90 and not re.search(r'\\b(sorry|error)\\b',b.decode(),re.I)
 matches=re.findall(r"'([^']+)' depends on axioms: \\[([^\\]]*)\\]",b.decode())
 exports=[{'theorem':n,'axioms':sorted(x.strip() for x in raw.split(',') if x.strip())} for n,raw in matches]
 assert exports==plan['exports']==run['exports']
 obj=out/'lean/Proofs'/(name+'.olean')
 assert hashlib.sha256(obj.read_bytes()).hexdigest()==run['object_sha256']
 assert obj.stat().st_size==run['object_bytes']>0
 assert (job/'sha').stat().st_mtime<=obj.stat().st_mtime<=(job/'exit').stat().st_mtime
files['endpoint.lean']=(repo/'proofs/Proofs/Erdos85FiniteDropCapstone.lean').read_bytes()
print(json.dumps({'status':'TERMINAL_ENDPOINT_CAPTURE_PASS','files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
'''
    prefix = "REPO=" + repr(REMOTE) + "\nAREA=" + repr(AREA) + "\nJOB=" + repr(args.job) + "\nCOMMIT=" + repr(args.commit) + "\n"
    raw = subprocess.check_output(["/Users/rwalters/.local/bin/e85-remote", "ssh",
                                   "python3 -B -c " + shlex.quote(prefix + code)])
    result = json.loads(raw)
    if result["status"] == "PENDING":
        print("PENDING")
        return
    files = {name: base64.b64decode(data) for name, data in result["files"].items()}
    files["capture.py"] = Path(__file__).read_bytes()
    audit = {"status": result["status"], "job": args.job, "execution_commit": args.commit,
             "retained_sha256": {name: hashlib.sha256(data).hexdigest() for name, data in files.items()},
             "scope": "Terminal job, exact source closure, fresh endpoint objects/logs and exact axiom sets; dependency hashes checked before/after by validate.py."}
    files["AUDIT.json"] = (json.dumps(audit, indent=2) + "\n").encode()
    target = ROOT / "evidence1"
    target.mkdir(exist_ok=False)
    for name, data in files.items():
        (target / name).write_bytes(data)
    print(json.dumps(audit))


if __name__ == "__main__":
    main()
