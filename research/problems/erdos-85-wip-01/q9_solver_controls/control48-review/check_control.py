"""Second-seat validation of a terminal graph control; never launches a solver."""
import argparse, hashlib, importlib.util, itertools, json
from pathlib import Path

GENERATOR=Path('/tmp/erdos85-sol1-q9-semiregular/generate.py')
ACCEPTED_GENERATOR='cafc21951969ed93a88f7db2a3b649c38deb53af3d81d6da10caeac5a2aef4a4'

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):return {'path':str(Path(p).resolve()),'sha256':sha(p)}
def read(p):return json.loads(Path(p).read_text())

def main():
    ap=argparse.ArgumentParser();ap.add_argument('result',type=Path);ap.add_argument('out',type=Path);args=ap.parse_args()
    assert not args.out.exists(), 'preserve earlier receipt'
    r=read(args.result); directory=Path(r['directory'])
    assert r['kind']=='control' and r['status']=='SAT' and r['exit_code']==10
    assert r['model_check']['status']=='PASS' and r['proof_logging'] is False
    assert (r['n'],r['d'],r['m']) in ((48,7,24),(63,8,21),(63,8,63))
    meta=read(directory/'generator-metadata.json');n,m,d=r['n'],r['m'],r['d']
    assert (meta['n'],meta['m'],meta['minimum_degree'])==(n,m,d)
    assert sha(directory/'generator-metadata.json')==r['metadata']['sha256']
    assert sha(directory/'input.cnf')==r['cnf']['sha256']==meta['cnf_sha256']
    assert sha(directory/'solver.log')==r['output']['sha256']
    assert meta['generator_sha256']==ACCEPTED_GENERATOR==sha(GENERATOR)
    spec=importlib.util.spec_from_file_location('accepted_generator',GENERATOR)
    gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
    c,reconstructed=gen.build(n,m,d)
    assert all(meta[k]==v for k,v in json.loads(json.dumps(reconstructed)).items())
    generated=('p cnf %d %d\n'%(c.nvars,len(c.clauses))+''.join(' '.join(map(str,x))+' 0\n' for x in c.clauses)).encode()
    assert generated==(directory/'input.cnf').read_bytes()
    values={}
    for line in (directory/'solver.log').read_text().splitlines():
        if line.startswith('v '):
            for x in map(int,line.split()[1:]):
                if x:
                    assert abs(x) not in values or values[abs(x)]==(x>0)
                    values[abs(x)]=x>0
    assert set(values)==set(range(1,c.nvars+1))
    assert all(any(values[abs(x)]==(x>0) for x in clause) for clause in c.clauses)
    pairs=set(itertools.combinations(range(n),2));adj=[set() for _ in range(n)]
    move=lambda u:m*(u//m)+(u%m+1)%m
    for o in meta['orbits']:
        orbit={tuple(e) for e in o['edges']}
        assert len(orbit)==len(o['edges']) and orbit<=pairs
        start=min(orbit);observed=set();pair=start
        while pair not in observed:
            observed.add(pair);pair=tuple(sorted(map(move,pair)))
        assert pair==start and observed==orbit
        pairs-=orbit
        if values[o['var']]:
            for u,v in orbit:adj[u].add(v);adj[v].add(u)
    assert not pairs
    assert all(u not in adj[u] and all(u in adj[v] for v in adj[u]) for u in range(n))
    degrees=list(map(len,adj));assert min(degrees)>=d
    if n==63:assert set(degrees)=={8}
    assert all(len(adj[u]&adj[v])<=1 for u,v in itertools.combinations(range(n),2))
    assert all({move(v) for v in adj[u]}==adj[move(u)] for u in range(n))
    for u in range(n):
        v=move(u);period=1
        while v!=u:v=move(v);period+=1
        assert period==m
    args.out.mkdir(parents=True)
    graph={'n':n,'m':m,'minimum_degree':min(degrees),'maximum_degree':max(degrees),
           'edges':sum(degrees)//2,'adjacency':[sorted(x) for x in adj]}
    (args.out/'graph.json').write_text(json.dumps(graph,indent=2)+'\n')
    verification={'status':'PASS','run_id':r['id'],'n':n,'d':d,'m':m,
                  'variables':c.nvars,'clauses':len(c.clauses),'edge_orbits':len(meta['orbits']),
                  'graph_parameters':{k:v for k,v in graph.items() if k!='adjacency'},
                  'source_result':pin(args.result),'map':pin(directory/'generator-metadata.json'),
                  'cnf':pin(directory/'input.cnf'),'model':pin(directory/'solver.log'),
                  'generator':pin(GENERATOR),'verifier':pin(__file__),
                  'scope':'second-seat control: full assignment/CNF/map binding, graph and free cyclic action checked'}
    (args.out/'verification.json').write_text(json.dumps(verification,indent=2)+'\n')
    receipt={'run_id':r['id'],'status':'PASS','reviewer':'codex-sol-2','n':n,'d':d,'m':m,
             'solver_output_sha256':sha(directory/'solver.log'),'graph':pin(args.out/'graph.json'),
             'verifier':pin(__file__),'verification_output':pin(args.out/'verification.json')}
    (args.out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(verification,indent=2))
if __name__=='__main__':main()
