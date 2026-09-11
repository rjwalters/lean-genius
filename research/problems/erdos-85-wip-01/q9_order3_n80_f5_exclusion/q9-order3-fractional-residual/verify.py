from pathlib import Path
import json
from model import model
p=Path(__file__).resolve().parent
rs=[r for r in map(json.loads,(p/'batch.jsonl').read_text().splitlines()) if r['status']=='EXACT_INFEASIBLE']+[r for r in map(json.loads,(p/'repaired.jsonl').read_text().splitlines()) if r['status']=='EXACT_REPAIRED_INFEASIBLE'];seen=set()
for r in rs:
 assert r['code'] not in seen;seen.add(r['code']);m=model(r['code']);cert=r['certificate'];assert len({i for i,v in cert})==len(cert);coeff=[0]*m['variables'];rhs=0
 for i,v in cert:
  assert isinstance(v,int) and v>0 and 0<=i<len(m['A']);rhs+=v*m['rhs'][i]
  for j,a in m['A'][i].items():coeff[j]+=v*a
 assert min(coeff)>=0 and rhs<0
out={'status':'PASS_EXACT_ARITHMETIC','certificates':len(seen),'model_construction':'shared model.py; independent model audit pending','remaining_unresolved_codes':[669268,24538199]};(p/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
