import json,subprocess,time,hashlib,resource
from pathlib import Path
p=Path(__file__).parent;repo=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration');proofs=repo/'proofs'
rows=json.loads((p/'h1-frozen-candidates.json').read_text())['rows'];row=next(r for r in rows if r['fleet_cnf_sha256'])
pairs=[(c,j) for c in range(8) for j in range(c+1,8) if j!=(c^1)]
table=p/'pilot-table.json';table.write_text(json.dumps([[list(k),v] for k,v in zip(pairs,row['table_values'],strict=True) if v])+'\n')
cnf=p/'pilot.cnf';log=p/'pilot-emit.log';cmd=['lake','env','lean','--run','Proofs/Erdos85OneHighV2CnfEmit.lean','emit',row['profile'],str(table)]
def limit():resource.setrlimit(resource.RLIMIT_FSIZE,(99_000_000,99_000_000))
t=time.monotonic()
with cnf.open('wb') as out,log.open('wb') as err:
 try:r=subprocess.run(cmd,cwd=proofs,stdout=out,stderr=err,timeout=120,preexec_fn=limit);rc=r.returncode
 except subprocess.TimeoutExpired:rc='TIMEOUT'
h=hashlib.sha256(cnf.read_bytes()).hexdigest();receipt={'tag':row['tag'],'profile':row['profile'],'command':cmd,'rc':rc,'seconds':time.monotonic()-t,'bytes':cnf.stat().st_size,'sha256':h,'expected_ledger_sha256':row['fleet_cnf_sha256'],'matches_ledger':h==row['fleet_cnf_sha256']}
(p/'pilot-emit-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
