from pathlib import Path
import importlib.util,itertools,json,hashlib,tempfile,time
p=Path(__file__).parent; src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls/decode_witness.py')
spec=importlib.util.spec_from_file_location('decoder',src);w=importlib.util.module_from_spec(spec);spec.loader.exec_module(w)
start=time.monotonic();tested=0;accepted=0
with tempfile.TemporaryDirectory() as tmp:
 out=Path(tmp)
 for n in range(2,6):
  for m in range(1,n+1):
   if n%m:continue
   todo=set(itertools.combinations(range(n),2));orbits=[]
   while todo:
    a,b=min(todo);orb={tuple(sorted(((a//m)*m+(a+k)%m,(b//m)*m+(b+k)%m))) for k in range(m)}
    assert orb<=todo;todo-=orb;orbits.append(sorted(orb))
   for bits in itertools.product([False,True],repeat=len(orbits)):
    edges=set(e for flag,orb in zip(bits,orbits) if flag for e in orb)
    deg=[sum(v in e for e in edges) for v in range(n)]
    # Direct cycle enumeration, independent of decoder common-neighbor criterion.
    c4=any(all(tuple(sorted(e)) in edges for e in [(a,b),(b,c),(c,d),(d,a)]) for a,b,c,d in itertools.permutations(range(n),4))
    for bound in sorted({0,min(deg),min(deg)+1}):
     lits=[i+1 if b else -i-1 for i,b in enumerate(bits)]
     cnf=('p cnf %d %d\n'%(len(bits),len(bits))+''.join(f'{x} 0\n' for x in lits)).encode();log=('s SATISFIABLE\nv '+' '.join(map(str,lits))+' 0\n').encode()
     meta=dict(schema=1,n=n,m=m,minimum_degree=bound,vertex_label='block*m+residue',variables=len(bits),clauses=len(bits),cnf_sha256=w.digest(cnf),orbits=[dict(var=i+1,edges=e) for i,e in enumerate(orbits)])
     raw=json.dumps(meta).encode();result=dict(id=0,status='SAT',n=n,m=m,d=bound,cnf={'sha256':w.digest(cnf)},metadata={'sha256':w.digest(raw)},output={'sha256':w.digest(log)})
     for name,data in [('input.cnf',cnf),('solver.log',log),('generator-metadata.json',raw),('result.json',json.dumps(result).encode())]:(out/name).write_bytes(data)
     try:g,r=w.decode(out);ok=True
     except ValueError:ok=False
     expected=not c4 and min(deg)>=bound
     assert ok==expected,(n,m,bits,bound,c4)
     if ok:assert {tuple(e) for e in g['edges']}==edges;accepted+=1
     tested+=1
control=src.parent/'runs/000-N48-m24';g,r=w.decode(control)
prior=json.loads(Path('/Users/rwalters/lean-genius-q9-known-values-20260911/control48-review/graph.json').read_text())
assert g['adjacency']==prior['adjacency'];assert len(g['edges'])==168
files=[src,src.parent/'test_decode_witness.py',Path(__file__)]+[control/name for name in ['result.json','input.cnf','generator-metadata.json','solver.log']]
(p/'input-pins.json').write_text(json.dumps({str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in files},indent=2)+'\n')
result=dict(status='PASS',complete_small_graph_cases=tested,accepted_cases=accepted,n_range=[2,5],all_dividing_action_orders=True,control48_edges=168,seconds=time.monotonic()-start,scope='Independent decoder algorithm review; new witnesses still require independent artifact and graph validation. No solver launched.')
(p/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
