"""Collect a pinned campaign job; never launches or retries computation."""
import argparse,base64,json,re,shlex,subprocess
from pathlib import Path
from common import ROOT,sha

def main():
    p=argparse.ArgumentParser();p.add_argument('--job',required=True);p.add_argument('--commit',required=True)
    p.add_argument('--preflight',action='store_true');p.add_argument('--output',required=True);a=p.parse_args()
    assert re.fullmatch(r'\d{8}T\d{6}-erdos85__h3-triple-formal-20261007-\d+',a.job)
    assert re.fullmatch(r'[a-f0-9]{40}',a.commit)
    assert Path(a.output).name==a.output and a.output not in ('.','..')
    common=(ROOT/'common.py').read_bytes();auditor=(ROOT/'audit_cloud.py').read_bytes()
    code='import types,sys\nm=types.ModuleType("common");m.__file__="/opt/e85/wt/erdos85__h3-triple-formal-20261007/research/problems/erdos-85-wip-01/h3_native_campaign_20261008/common.py";sys.modules[m.__name__]=m\n'
    code+='exec(compile('+repr(common)+',m.__file__,"exec"),m.__dict__)\n'
    code+='exec(compile('+repr(auditor)+',"audit_cloud.py","exec"))\nmain('+repr(vars(a))+')'
    remote='import base64;exec(compile(base64.b64decode('+repr(base64.b64encode(code.encode()).decode())+'),"campaign_audit","exec"))'
    r=subprocess.run(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(remote)],capture_output=True)
    if r.returncode:print(r.stderr.decode());raise SystemExit(r.returncode)
    bundle=json.loads(r.stdout)
    if bundle.get('status')=='PENDING':print(json.dumps(bundle));return
    audit=bundle['audit'];files={n:base64.b64decode(b) for n,b in bundle['files'].items()}
    for n,b in files.items():assert sha(b)==audit['retained_sha256'][n]
    files['collector.py']=Path(__file__).read_bytes();files['auditor.py']=auditor
    assert files['common.py']==common
    audit['retained_sha256']={n:sha(b) for n,b in files.items()}
    files['AUDIT.json']=(json.dumps(audit,indent=2)+'\n').encode()
    for n,b in files.items():
        out=ROOT/a.output/n;out.parent.mkdir(parents=True,exist_ok=True)
        if out.exists():assert out.read_bytes()==b,'Refusing evidence overwrite: '+n
        else:out.write_bytes(b)
    print(audit['status']);print('Accepted new residues:',audit.get('accepted_new_residues',[]))
if __name__=='__main__':main()
