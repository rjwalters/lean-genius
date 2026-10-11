"""Collect independent cloud acceptance of the H3-discharged capstone."""
import argparse,base64,json,re,shlex,subprocess,zlib
from pathlib import Path
from prepare import ROOT,sha
def main():
    p=argparse.ArgumentParser();p.add_argument('--job',required=True);p.add_argument('--commit',required=True);a=p.parse_args()
    assert re.fullmatch(r'\d{8}T\d{6}-erdos85__h3-triple-formal-20261007-\d+',a.job)
    assert re.fullmatch('[a-f0-9]{40}',a.commit)
    area='/opt/e85/wt/erdos85__h3-triple-formal-20261007/research/problems/erdos-85-wip-01/order49_h3_closed_capstone_20261008/'
    code='import types,sys\nm=types.ModuleType("prepare");m.__file__='+repr(area+'prepare.py')+';sys.modules[m.__name__]=m\n'
    code+='exec(compile('+repr((ROOT/'prepare.py').read_bytes())+',m.__file__,"exec"),m.__dict__)\n'
    auditor=(ROOT/'audit_cloud.py').read_bytes()
    code+='exec(compile('+repr(auditor)+',"audit_cloud.py","exec"))\nmain('+repr(vars(a))+')'
    remote='import base64,zlib;exec(compile(zlib.decompress(base64.b64decode('+repr(base64.b64encode(zlib.compress(code.encode())).decode())+')),"capstone_audit","exec"))'
    r=subprocess.run(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(remote)],capture_output=True)
    if r.returncode:print(r.stderr.decode());raise SystemExit(r.returncode)
    bundle=json.loads(r.stdout)
    if bundle.get('status')=='PENDING':print(json.dumps(bundle));return
    report=bundle['audit'];files={n:base64.b64decode(b) for n,b in bundle['files'].items()}
    for n,b in files.items():assert sha(b)==report['retained_sha256'][n]
    assert files['audit_cloud.py']==auditor and files['capture.py']==Path(__file__).read_bytes()
    files['AUDIT.json']=(json.dumps(report,indent=2)+'\n').encode()
    for n,b in files.items():
        path=ROOT/'evidence1'/n;path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():assert path.read_bytes()==b,'Refusing changed evidence: '+n
        else:path.write_bytes(b)
    print(report['status']);print('Exact axiom counts:',[len(x['axioms']) for x in report['exports']]);print('Elapsed:',report['elapsed_seconds'])
if __name__=='__main__':main()
