from pathlib import Path
import json,hashlib,importlib.util,itertools as it,time,gc
p=Path(__file__).parent;t=time.monotonic();generator=Path('/tmp/erdos85-sol1-q9-semiregular/generate.py');spec=importlib.util.spec_from_file_location('reviewed_generator',generator);g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);gh=hashlib.sha256(generator.read_bytes()).hexdigest();assert gh=='cafc21951969ed93a88f7db2a3b649c38deb53af3d81d6da10caeac5a2aef4a4';out=[]
for n,ms in [(80,[10,8,5,4,2,1]),(78,[6,3,2,1])]:
 for m in ms:
  q=Path(f'/tmp/erdos85-sol1-q9-n{n}-m{m}') if m!=1 else p.parent/f'q9-m1-n{n}-size-check';meta=json.loads((q/'map.json').read_text());cnf=q/'graph.cnf';actual=hashlib.sha256(cnf.read_bytes()).hexdigest();assert actual==meta['cnf_sha256'];assert meta['generator_sha256']==gh and (meta['n'],meta['m'],meta['minimum_degree'])==(n,m,9)
  c,fresh=g.build(n,m,9);h=hashlib.sha256();h.update(f'p cnf {c.nvars} {len(c.clauses)}\n'.encode())
  for row in c.clauses:h.update((' '.join(map(str,row))+' 0\n').encode())
  assert h.hexdigest()==actual;assert all(meta[k]==v for k,v in json.loads(json.dumps(fresh)).items());seen=set()
  for o in meta['orbits']:
   edges=set(map(tuple,o['edges']));assert not seen.intersection(edges);seen.update(edges);u,v=next(iter(edges))
   def shift(x,k):return x//m*m+(x%m+k)%m
   assert edges=={tuple(sorted((shift(u,k),shift(v,k)))) for k in range(m)}
  assert seen==set(it.combinations(range(n),2))
  out.append(dict(n=n,m=m,status='PASS',path=str(q),variables=c.nvars,clauses=len(c.clauses),edge_variables=len(meta['orbits']),bytes=cnf.stat().st_size,cnf_sha256=actual,map_sha256=hashlib.sha256((q/'map.json').read_bytes()).hexdigest(),generator_sha256=gh))
  del c,fresh;gc.collect()
x=dict(status='PASS',seconds=time.monotonic()-t,instances=out,scope='Reviewed-generator byte-for-byte CNF/map regeneration and independent translation edge-orbit partition; no solver verdict, no new encoding audit');(p/'results.json').write_text(json.dumps(x,indent=2)+'\n');print(dict(status=x['status'],seconds=x['seconds'],instances=len(out)))
