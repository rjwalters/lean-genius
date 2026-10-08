"""Capture a pinned terminal H3 stratum build and retain immutable evidence."""
import argparse,base64,json,re,shlex,subprocess
from pathlib import Path
from transfer_pair import ROOT,sha

def main():
    p=argparse.ArgumentParser();p.add_argument('--job',required=True);p.add_argument('--commit',required=True)
    p.add_argument('--triple-audit-sha',required=True);p.add_argument('--transfer-receipt-sha',required=True)
    p.add_argument('--output',default='stratum-evidence1');a=p.parse_args()
    assert re.fullmatch(r'\d{8}T\d{6}-erdos85__h3-triple-formal-20261007-\d+',a.job)
    assert re.fullmatch(r'[a-f0-9]{40}',a.commit)
    assert all(re.fullmatch(r'[a-f0-9]{64}',h) for h in (a.triple_audit_sha,a.transfer_receipt_sha))
    assert Path(a.output).name==a.output and a.output not in ('.','..')
    area='/opt/e85/wt/erdos85__h3-triple-formal-20261007/research/problems/erdos-85-wip-01/h3_stratum_integration_20261008/'
    code='import types,sys\n';scripts={}
    for name in ('transfer_pair','stratum_inputs'):
        data=(ROOT/(name+'.py')).read_bytes();scripts[name+'.py']=data
        code+='m=types.ModuleType('+repr(name)+');m.__file__='+repr(area+name+'.py')+';sys.modules[m.__name__]=m\n'
        code+='exec(compile('+repr(data)+',m.__file__,"exec"),m.__dict__)\n'
    auditor=(ROOT/'audit_stratum_cloud.py').read_bytes()
    code+='exec(compile('+repr(auditor)+',"audit_stratum_cloud.py","exec"))\nmain('+repr(vars(a))+')'
    remote='import base64;exec(compile(base64.b64decode('+repr(base64.b64encode(code.encode()).decode())+'),"stratum_audit","exec"))'
    r=subprocess.run(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(remote)],capture_output=True)
    if r.returncode:print(r.stderr.decode());raise SystemExit(r.returncode)
    bundle=json.loads(r.stdout)
    if bundle.get('status')=='PENDING':print(json.dumps(bundle));return
    report=bundle['audit'];files={n:base64.b64decode(b) for n,b in bundle['files'].items()}
    for name,data in files.items():assert sha(data)==report['retained_sha256'][name]
    for name,data in scripts.items():assert files[name]==data
    files['auditor.py']=auditor;files['collector.py']=Path(__file__).read_bytes()
    report['retained_sha256']={n:sha(b) for n,b in files.items()}
    files['AUDIT.json']=(json.dumps(report,indent=2)+'\n').encode()
    for name,data in files.items():
        path=ROOT/a.output/name;path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():assert path.read_bytes()==data,'Refusing changed evidence: '+name
        else:path.write_bytes(data)
    print(report['status']);print('Theorem:',report.get('theorem'));print('Axiom count:',len(report.get('axioms',[])))
if __name__=='__main__':main()
