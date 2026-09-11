from pathlib import Path
import json,gzip,hashlib,sqlite3
P=Path(__file__).parent;S=P.parent/'h7-a6-f15-host-pass';assert not (P/'source-leaves.jsonl.gz').exists()
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);status,resolution=c.execute('select status,resolution from review_requests where id=2128').fetchone();assert status=='resolved' and resolution.startswith('PASS')
for f,h in json.loads((S/'pins.json').read_text()).items():assert hashlib.sha256((S/f).read_bytes()).hexdigest()==h
summary=json.loads((S/'results.json').read_text());assert summary['counts']=={'COMPLETE':4536} and summary['unvisited']==0 and not summary['unknown'];seen=[];groups=0
with gzip.open(P/'source-leaves.jsonl.gz','wt') as out:
 for shard in summary['shards']:
  for line in gzip.open(S/shard,'rt'):
   r=json.loads(line);cert=r['receipt'];assert cert['status']=='COMPLETE' and cert['empty_vertices']==list(range(42,49));hosts=cert['solutions']
   for j,ms in enumerate(hosts):
    used=0
    for m in ms:assert not m&~(((1<<21)-1)<<21) and not m&used;used|=m
    assert used.bit_count()==12;seen.append([r['global_index'],j])
   if hosts:out.write(json.dumps(dict(global_index=r['global_index'],hosts=hosts),separators=(',',':'))+'\n');groups+=1
assert seen==json.loads((S/'survivors.json').read_text()) and len(seen)==142812
(P/'source-indices.json').write_bytes((S/'survivors.json').read_bytes());(P/'source-bases.jsonl.gz').write_bytes((S/'inputs.jsonl.gz').read_bytes());(P/'source-pins.json').write_bytes((S/'pins.json').read_bytes());(P/'export-results.json').write_text(json.dumps(dict(status='PASS',leaves=len(seen),groups=groups,exact_source_masks=True))+'\n');print('PASS',len(seen),'leaves in',groups,'groups')
