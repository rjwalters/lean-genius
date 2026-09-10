import subprocess,json,time,hashlib,resource
from pathlib import Path
p=Path(__file__).parent;binary=Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex/h1fleet/v3freight-rebuild-20260905/stage/freight/v2cnf');image='sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6'
assert hashlib.sha256(binary.read_bytes()).hexdigest()=='4bd9604c6d670ad65a8ca332a26dbf35132418634a3b0678c177c8b2cfff4bf6'
name='erdos85-sol1-native-input-pilot-20260910';cnf=p/'native-pilot.cnf'
base=['docker','run','--rm','--name',name,'--read-only','--network','none','--memory','8g','--cpus','1','--pids-limit','64','--mount',f'type=bind,src={binary},dst=/v2cnf,readonly','--mount',f'type=bind,src={p},dst=/inputs,readonly',image,'/v2cnf']
def run(mode):
 cmd=base+[mode,'2','/inputs/pilot-table.json']+(['/inputs/native-pilot.cnf'] if mode=='check' else [])
 t=time.monotonic();outfile=cnf if mode=='emit' else p/'native-check.log'
 with outfile.open('wb') as out,(p/f'native-{mode}.err').open('wb') as err:
  try:r=subprocess.run(cmd,stdout=out,stderr=err,timeout=120);rc=r.returncode
  except subprocess.TimeoutExpired:
   subprocess.run(['docker','rm','-f',name],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=15);rc='TIMEOUT'
 return {'command':cmd,'rc':rc,'seconds':time.monotonic()-t}
r=run('emit');r['bytes']=cnf.stat().st_size;r['sha256']=hashlib.sha256(cnf.read_bytes()).hexdigest();r['expected_ledger_sha256']='63ba3e99aa19f2ad56784f704afee5569808af699cd88d31a8ca54634e2e6f69';r['matches_ledger']=r['sha256']==r['expected_ledger_sha256']
(p/'native-emit-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
if r['rc']==0 and r['matches_ledger']:
 c=run('check');c['stdout']=(p/'native-check.log').read_text();(p/'native-check-receipt.json').write_text(json.dumps(c,indent=2)+'\n');print(json.dumps(c),flush=True)
