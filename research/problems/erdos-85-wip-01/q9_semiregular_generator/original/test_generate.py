import itertools,json,time
from generate import build

def graph_ok(n,edges,d):
    adj=[set() for _ in range(n)]
    for u,v in edges: adj[u].add(v);adj[v].add(u)
    return min(map(len,adj))>=d and all(len(adj[u]&adj[v])<2 for u in range(n) for v in range(u))

def main():
    start=time.monotonic(); tested=0; cases=[]
    for n,m in [(3,1),(4,1),(4,2),(4,4),(5,5),(6,2),(6,3),(6,6),(8,4)]:
        for d in range(min(n,4)):
            c,meta=build(n,m,d); vs=[o['var'] for o in meta['orbits']]
            for bits in itertools.product((False,True),repeat=len(vs)):
                assignment=dict(zip(vs,bits)); vals=c.extension(assignment)
                sat=all(any(vals[abs(x)]==(x>0) for x in clause) for clause in c.clauses)
                edges=[e for o in meta['orbits'] if assignment[o['var']] for e in o['edges']]
                expected=graph_ok(n,edges,d)
                assert sat==expected,(n,m,d,bits)
                tested+=1
            cases.append([n,m,d,2**len(vs)])
    result={'status':'PASS','assignments':tested,'cases':cases,'seconds':time.monotonic()-start,'scope':'all orbit assignments; functional Tseitin extension compared with independent degree/common-neighbour checks'}
    open('test-results.json','w').write(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
