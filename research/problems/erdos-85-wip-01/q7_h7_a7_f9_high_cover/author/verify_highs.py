import pathlib,json,itertools,time,collections
P=pathlib.Path(__file__).parent;S=P.parent/'h7-a7-noncycle-singleton-projection';cover=json.loads((S/'results.json').read_text());done=json.loads((S/'completion-results.json').read_text());data=json.loads((P/'high-results.json').read_text());source={(r['source_index'],j):es for r in done['results'] if r['F_index']==9 and r['status']=='COMPLETE' for j,es in enumerate(r['solutions'])};seen=set();count=positive=0;start=time.monotonic()
for i,r in enumerate(data['results']):
 assert time.monotonic()-start<60 and r['status']=='COMPLETE' and r['case_index']==i;key=(r['source_index'],r['singleton_index']);assert key not in seen;seen.add(key);rep=cover['representatives'][key[0]];g=[set() for _ in range(21)]
 def add(u,v):g[u].add(v);g[v].add(u)
 for u,v in rep['F_edges']+source[key]:add(u,v)
 for s,hs in enumerate(rep['singleton_hosts'],7):
  for e in hs:add(s,e)
 # Precompute forbidden pair relation by counting shared neighbors directly.
 ok={(h,d) for h in range(7) for d in range(7) if 7+d not in g[14+h] and sum(v in g[7+d] for v in g[14+h])==0}
 expected={p for p in itertools.permutations(range(7)) if all((h,d) in ok for h,d in enumerate(p))};assert expected==set(map(tuple,r['pairings'])) and len(expected)==len(r['pairings']);count+=len(expected);positive+=bool(expected)
assert seen==set(source) and count==28336 and positive==1472
out=dict(status='PASS',cases=len(seen),pairings=count,positive=positive,negative=len(seen)-positive,seconds=time.monotonic()-start);(P/'high-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
