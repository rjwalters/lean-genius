"""Capture H7 review inputs using only AWS read operations; no live writes."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import hashlib,json,subprocess
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PIN='729127aa817263475e7aa0c65c3db34a65da3389'
AREA='research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008'
AWS=['aws','--profile','2am-admin','--region','us-east-1']
BUCKET='2am-erdos85-certs'
def main():
    out=ROOT/'snapshot1';out.mkdir(exist_ok=False)
    commands={
      'instances.json':['ec2','describe-instances','--filters','Name=tag:project,Values=e85-h7hsb-20261008,e85-h7hsb-20261008-canary,e85-h7hsb-controller'],
      'fleets.json':['ec2','describe-fleets','--fleet-ids','fleet-d57fe55e-20a4-4cb1-ba3e-3562f2608b82','fleet-dae91a7e-68ca-4e6c-b946-247aa86069fb'],
      'canary-template.json':['ec2','describe-launch-template-versions','--launch-template-id','lt-0dcb4a71cfd5de065','--versions','3'],
      'main-template.json':['ec2','describe-launch-template-versions','--launch-template-id','lt-07329f425d7867404','--versions','1'],
    }
    for tag in ('main','canary'):
        prefix='sat49/h7hsb-20261008'+('-canary' if tag=='canary' else '')
        commands[tag+'-objects.json']=['s3api','list-objects-v2','--bucket',BUCKET,'--prefix',prefix+'/']
        commands[tag+'-last-report.json']=['s3','cp','--only-show-errors','s3://'+BUCKET+'/'+prefix+'/host/last_report.json','-']
    def read(item):
        name,args=item;r=subprocess.run(AWS+args,capture_output=True,check=True)
        json.loads(r.stdout);(out/name).write_bytes(r.stdout)
    started=datetime.now(timezone.utc).isoformat()
    with ThreadPoolExecutor(max_workers=4) as pool:list(pool.map(read,commands.items()))
    canary='s3://'+BUCKET+'/sat49/h7hsb-20261008-canary/'
    # Download only small operational evidence and result receipts, never proof streams.
    args=['s3','sync','--only-show-errors',canary,str(out/'canary'),'--exclude','*']
    for glob in ('ledger/*','results/*','partial/*','control/*','host/*','nodes/*','transitions/*'):
        args+=['--include',glob]
    subprocess.run(AWS+args,check=True)
    repo=ROOT.parents[3];sources=out/'source';sources.mkdir()
    for name in ('cert_controller.py','cert_worker.py','cert_batch.py','cert_item.py','cert_bootstrap.sh','h7_common.py','test_campaign.py'):
        (sources/name).write_bytes(subprocess.check_output(['git','-C',str(repo),'show',PIN+':'+AREA+'/'+name]))
    p='research/problems/erdos-85-wip-01/phase_b_h1_verdict_cloud_20260921/controller.py'
    (sources/'base_controller.py').write_bytes(subprocess.check_output(['git','-C',str(repo),'show',PIN+':'+p]))
    report={'status':'READ_ONLY_SNAPSHOT_CAPTURED_NOT_ACCEPTANCE','worker_pin':PIN,'started_utc':started,'finished_utc':datetime.now(timezone.utc).isoformat(),'aws_commands':commands,'download_command':args,'retained_sha256':{str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.rglob('*')) if p.is_file()}}
    (out/'CAPTURE.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],'files',len(report['retained_sha256']))
if __name__=='__main__':main()
