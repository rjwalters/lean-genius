import gzip,hashlib,json,time
from pathlib import Path
D=Path(__file__).parent;P=Path('/Users/rwalters/lean-genius-h7-a6-f14-incidence-native-sol2-20260915');R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic();fixtures=read(P/'fixtures.json');count=0;manifest_hashes={}
for fi in [12,14]:
 source=R/'q7_h7_a6_f12_host/original' if fi==12 else Path('/Users/rwalters/lean-genius-h7-a6-f14-sol1-20260915')
 host=source if fi==12 else source/'hosts';manifest=source/('pins.json' if fi==12 else 'host-pins.json')
 for n,h in read(manifest).items():assert sha(source/n)==h
 manifest_hashes[str(manifest)]=sha(manifest)
 fs={(x['global_index'],x['leaf_index']):x for x in fixtures if x['source_F']==fi};assert len(fs)==sum(x['source_F']==fi for x in fixtures)
 if fi==12:expected={(x['global_index'],x['leaf_index']) for x in read(R/'q7_h7_a6_f12_closure/author/results.json')['records']}
 else:
  keys=read(host/'survivors.json');expected={tuple(keys[i*(1757882-1)//127]) for i in range(128)}
 assert set(fs)==expected
 wanted={gid for gid,j in fs};inputs={}
 for row in map(json.loads,gzip.open(source/'inputs.jsonl.gz','rt')):
  if row['global_index'] in wanted:inputs[row['global_index']]=row['neighbors']
 seen=set()
 for name in read(host/'results.json')['shards']:
  for row in map(json.loads,gzip.open(host/name,'rt')):
   gid=row['global_index']
   if gid not in wanted:continue
   assert row['receipt']['status']=='COMPLETE'
   for j,ms in enumerate(row['receipt']['solutions']):
    if (gid,j) not in fs:continue
    g=[set(ns) for ns in inputs[gid]]
    for e,mask in enumerate(ms,42):
     for v in range(49):
      if mask>>v&1:g[e].add(v);g[v].add(e)
    assert fs[gid,j]['graph']==[sum(1<<v for v in ns) for ns in g]
    seen.add((gid,j));count+=1
   assert time.monotonic()-start<60
 assert seen==expected
out={'status':'PASS_EXACT_FIXTURE_SOURCE_JOIN','fixtures':count,'seconds':time.monotonic()-start,'fixture_sha256':sha(P/'fixtures.json'),'source_manifests':manifest_hashes,'scope':'Exact source and host receipt reconstruction of all 151 qualification fixtures; F14 fixtures belong to accepted negative prefix.'}
(D/'SOURCE_REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
