"""One bounded integration-fixture run; not a whole-shape search."""
import hashlib
import json
import time
from pathlib import Path
import api
import fixtures
import check_receipt

P=Path(__file__).parent
inputs=fixtures.load()
with (P/'fixture-launch.json').open('x') as out:
    json.dump({'max_nodes':100000,'aggregate_seconds':60,'inputs':inputs,
               'native_sha256':hashlib.sha256((P/'hosts.dylib').read_bytes()).hexdigest()},out,indent=2)
deadline=time.monotonic()+60;results=[]
for fixture in inputs:
    remaining=deadline-time.monotonic();assert remaining>0
    receipt=api.enumerate_hosts(fixture['adjacency'],max_nodes=100000,seconds=remaining)
    checked=check_receipt.check(fixture['adjacency'],receipt,seconds=max(0,deadline-time.monotonic()))
    assert receipt['nodes']<=100001
    results.append({'fixture':{k:v for k,v in fixture.items() if k!='adjacency'},'receipt':receipt,'checked':checked})
(P/'fixture-results.json').write_text(json.dumps(results)+'\n')
summary=[dict(x['fixture'],status=x['receipt']['status'],nodes=x['receipt']['nodes'],**x['checked']) for x in results]
(P/'fixture-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
assert api.enumerate_hosts(inputs[0]['adjacency'],max_nodes=0)['status']=='UNKNOWN'
print(json.dumps(summary,indent=2))
