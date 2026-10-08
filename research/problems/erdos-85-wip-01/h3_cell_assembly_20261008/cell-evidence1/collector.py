"""Collect the pinned H3 cell assembly/preflight job; never compile or retry."""
import argparse,base64,json,re,shlex,subprocess
from pathlib import Path
from common import ROOT,sha
def main():
    p=argparse.ArgumentParser();p.add_argument('--job',required=True);p.add_argument('--commit',required=True)
    p.add_argument('--preflight',action='store_true');p.add_argument('--output',required=True);a=p.parse_args()
    assert re.fullmatch(r'\d{8}T\d{6}-erdos85__h3-triple-formal-20261007-\d+',a.job)
    assert re.fullmatch(r'[a-f0-9]{40}',a.commit)
    assert Path(a.output).name==a.output and a.output not in ('.','..')
    helpers={n:(ROOT/(n+'.py')).read_bytes() for n in ('prepare','common')}
    auditor=(ROOT/'audit_cloud.py').read_bytes();code='import types,sys\n'
    remote_root='/opt/e85/wt/erdos85__h3-triple-formal-20261007/research/problems/erdos-85-wip-01/h3_cell_assembly_20261008/'
    for n,data in helpers.items():
        code+='m=types.ModuleType('+repr(n)+');m.__file__='+repr(remote_root+n+'.py')+';sys.modules[m.__name__]=m\n'
        code+='exec(compile('+repr(data)+',m.__file__,"exec"),m.__dict__)\n'
    code+='exec(compile('+repr(auditor)+',"audit_cloud.py","exec"))\nmain('+repr(vars(a))+')'
    remote='import base64;exec(compile(base64.b64decode('+repr(base64.b64encode(code.encode()).decode())+'),"cell_audit","exec"))'
    result=subprocess.run(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(remote)],capture_output=True)
    if result.returncode:print(result.stderr.decode());raise SystemExit(result.returncode)
    bundle=json.loads(result.stdout)
    if bundle.get('status')=='PENDING':print(json.dumps(bundle));return
    audit=bundle['audit'];files={n:base64.b64decode(b) for n,b in bundle['files'].items()}
    for n,b in files.items():assert sha(b)==audit['retained_sha256'][n]
    for n,b in helpers.items():assert files[n+'.py']==b
    assert files['audit_cloud.py']==auditor
    files['collector.py']=Path(__file__).read_bytes();audit['retained_sha256']={n:sha(b) for n,b in files.items()}
    files['AUDIT.json']=(json.dumps(audit,indent=2)+'\n').encode()
    for n,b in files.items():
        path=ROOT/a.output/n;path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():assert path.read_bytes()==b,'Refusing evidence overwrite: '+n
        else:
            with path.open('xb') as f:f.write(b)
    print(audit['status'])
if __name__=='__main__':main()
