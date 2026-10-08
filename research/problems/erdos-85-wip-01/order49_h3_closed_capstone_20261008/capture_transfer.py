"""Retain a terminal object transfer and a second read-only cache inspection."""
import argparse,base64,json,re,shlex,subprocess
from prepare import ROOT,sha
def main():
    p=argparse.ArgumentParser();p.add_argument('--job',required=True);p.add_argument('--commit',required=True);a=p.parse_args()
    assert re.fullmatch(r'\d{8}T\d{6}-erdos85__h3-triple-formal-20261007-\d+',a.job)
    assert re.fullmatch('[a-f0-9]{40}',a.commit)
    code='''from pathlib import Path
import base64,hashlib,json,re,subprocess
repo=Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
area='research/problems/erdos-85-wip-01/order49_h3_closed_capstone_20261008'
root=repo/area;job=Path('/opt/e85/jobs')/CONFIG['job']
sha=lambda b:hashlib.sha256(b).hexdigest()
assert (job/'exit').read_text().strip()=='0'
assert not Path('/proc/'+(job/'pid').read_text().strip()).exists()
files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
assert re.findall(r'^\\[e85\\] commit ([a-f0-9]{40}) ',files['job.log'].decode(),re.M)==[CONFIG['commit']]
for n in ('PLAN.json','prepare.py','transfer.py','supplementary.json'):
 b=subprocess.check_output(['git','-C',str(repo),'show',CONFIG['commit']+':'+area+'/'+n]);assert b==(root/n).read_bytes();files[n]=b
files['transfer.json']=(root/'transfer.json').read_bytes();receipt=json.loads(files['transfer.json'])
assert receipt['status']=='CAPSTONE_OBJECT_TRANSFER_VERIFIED' and receipt['plan_sha256']==sha(files['PLAN.json'])
inspection=subprocess.check_output(['sudo','python3','-B',str(root/'transfer.py')]);files['inspection.json']=inspection
actual=json.loads(inspection);assert actual['status']=='CAPSTONE_OBJECT_TRANSFER_INSPECTION_PASS'
assert actual['objects']==receipt['after'] and all(x['destination_exists'] for x in actual['objects']) and len(actual['objects'])==500
assert actual['plan_sha256']==receipt['plan_sha256']
report={'status':'CAPSTONE_TRANSFER_ARTIFACT_AUDIT_PASS','job':job.name,'execution_commit':CONFIG['commit'],'objects':500,'created':len(receipt['created']),'retained_sha256':{n:sha(b) for n,b in files.items()}}
print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
'''
    code='CONFIG='+repr(vars(a))+'\n'+code
    remote='import base64;exec(compile(base64.b64decode('+repr(base64.b64encode(code.encode()).decode())+'),"transfer_audit","exec"))'
    r=subprocess.run(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(remote)],capture_output=True)
    if r.returncode:print(r.stderr.decode());raise SystemExit(r.returncode)
    bundle=json.loads(r.stdout);report=bundle['audit'];files={n:base64.b64decode(b) for n,b in bundle['files'].items()}
    for n,b in files.items():assert sha(b)==report['retained_sha256'][n]
    files['collector.py']=__import__('pathlib').Path(__file__).read_bytes();report['retained_sha256']={n:sha(b) for n,b in files.items()}
    files['AUDIT.json']=(json.dumps(report,indent=2)+'\n').encode()
    for n,b in files.items():
        path=ROOT/'transfer-evidence1'/n;path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():assert path.read_bytes()==b,'Refusing changed evidence: '+n
        else:path.write_bytes(b)
    dst=ROOT/'transfer.json'
    if dst.exists():assert dst.read_bytes()==files['transfer.json']
    else:dst.write_bytes(files['transfer.json'])
    print(report['status'],'objects',report['objects'],'created',report['created'])
if __name__=='__main__':main()
