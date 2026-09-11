"""Decode a solver model; check the expanded graph without SAT auxiliaries."""
import argparse,hashlib,json
from pathlib import Path

def decode(meta,model):
    assignment={}
    for line in model.splitlines():
        if line.startswith('v '):
            for x in map(int,line.split()[1:]):
                if not x: continue
                assert abs(x) not in assignment or assignment[abs(x)]==(x>0)
                assignment[abs(x)]=x>0
    n=meta['n'];m=meta['m'];adj=[set() for _ in range(n)]
    for o in meta['orbits']:
        assert o['var'] in assignment,'missing edge variable'
        if assignment[o['var']]:
            for u,v in o['edges']: adj[u].add(v);adj[v].add(u)
    assert all(u not in adj[u] for u in range(n))
    assert all(u in adj[v] for u in range(n) for v in adj[u])
    assert min(map(len,adj))>=meta['minimum_degree']
    assert all(len(adj[u]&adj[v])<=1 for u in range(n) for v in range(u)), 'C4'
    translate=lambda u:(u//m)*m+(u%m+1)%m
    assert all({translate(v) for v in adj[u]}==adj[translate(u)] for u in range(n))
    return {'n':n,'m':m,'minimum_degree':min(map(len,adj)),'maximum_degree':max(map(len,adj)),'edges':sum(map(len,adj))//2,'adjacency':[sorted(a) for a in adj]}

def main():
    p=argparse.ArgumentParser();p.add_argument('mapping',type=Path);p.add_argument('model',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    assert not a.output.exists()
    graph=decode(json.loads(a.mapping.read_text()),a.model.read_text())
    graph['map_sha256']=hashlib.sha256(a.mapping.read_bytes()).hexdigest();graph['model_sha256']=hashlib.sha256(a.model.read_bytes()).hexdigest()
    a.output.write_text(json.dumps(graph,indent=2)+'\n');print({k:v for k,v in graph.items() if k!='adjacency'})
if __name__=='__main__':main()
