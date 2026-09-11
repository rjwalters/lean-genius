from pathlib import Path
import json,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();sym=json.loads((p/'results.json').read_text());pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};total=0
for c in sym['records']:
 ci=c['class']
 def supports(ri):
  ss=[dom[ci]['high3'][j] for j in pack[ci]['survivors'][ri]['high3']]
  return [frozenset(t) for s in ss for t in (s,[e^1 for e in s])]
 for o in c['orbits']:
  source=graphs[o['representative_root']];S=supports(o['representative_source_root'])
  for member in o['members']:
   assert time.monotonic()-start<30
   f=c['automorphisms'][member['automorphism']];target=graphs[member['root']];T=supports(member['source_root']);vmap=[T.index(frozenset(f[e] for e in s)) for s in S];assert all(vmap[v^1]==(vmap[v]^1) for v in range(10))
   expected={tuple(sorted(tuple(sorted(e)) for e in g['edges'])):g['Q_domains'] for g in target['survivors']};actual={}
   for g in source['survivors']:
    key=tuple(sorted(tuple(sorted((vmap[v],vmap[w]))) for v,w in g['edges']));rows=[None]*10
    for v,ds in enumerate(g['Q_domains']):rows[vmap[v]]=sorted(sum(1<<f[e] for e in range(10) if m>>e&1) for m in ds)
    actual[key]=rows
   expected={key:[sorted(ds) for ds in rows] for key,rows in expected.items()};assert actual==expected;total+=len(expected)
out={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'representative_packings':sum(len(c['orbits']) for c in sym['records']),'covered_packings':sum(len(o['members']) for c in sym['records'] for o in c['orbits']),'covered_high_matchings':total};(p/'transport.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
