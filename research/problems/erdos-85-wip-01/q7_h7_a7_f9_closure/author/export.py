import pathlib,json,gzip,collections,hashlib
P=pathlib.Path(__file__).parent;S=P.parent/'h7-a7-f9-host-pass';assert not (P/'source-leaves.jsonl.gz').exists()
for f,h in json.loads((S/'pins.json').read_text()).items():assert hashlib.sha256((S/f).read_bytes()).hexdigest()==h
summary=json.loads((S/'results.json').read_text());assert summary['unvisited']==0 and not summary['unknown_high_graphs'];groups=collections.defaultdict(list);seen=[];allowed=((1<<21)-1)<<21
for shard in summary['receipt_shards']:
 with gzip.open(S/shard,'rt') as stream:
  for line in stream:
   r=json.loads(line);cert=r['receipt'];assert cert['status']=='COMPLETE' and cert['empty_vertices']==list(range(42,49))
   for li,leaf in enumerate(cert['solutions']):
    used=0
    for mask in leaf:assert mask&~allowed==0 and not mask&used;used|=mask
    assert used.bit_count()==14
    ci,pi=r['case_index'],r['pairing_index'];groups[ci].append(dict(pairing_index=pi,leaf_index=li,hosts=[m>>21 for m in leaf]));seen.append([ci,pi,li])
assert seen==json.loads((S/'survivors.json').read_text()) and len(seen)==99224
with gzip.open(P/'source-leaves.jsonl.gz','wt') as stream:
 for ci,items in sorted(groups.items()):stream.write(json.dumps(dict(case_index=ci,items=items),separators=(',',':'))+'\n')
(P/'source-indices.json').write_text(json.dumps(seen,separators=(',',':'))+'\n');(P/'source-pins.json').write_bytes((S/'pins.json').read_bytes());print(dict(leaves=len(seen),groups=len(groups),bytes=(P/'source-leaves.jsonl.gz').stat().st_size))
