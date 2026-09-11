"""Complete local two-group check; no other attached groups or full G search."""
import collections
import itertools
import json
import time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
R=[(0,1)]+[(0,2*i) for i in range(1,5)]+[(1,2*i+1) for i in range(1,5)]+[(2,4),(3,5),(6,8),(7,9)]
def matchings(vertices):
    if not vertices:
        yield [];return
    a,*rest=vertices
    for b in rest:
        for m in matchings([v for v in rest if v!=b]):yield [(a,b)]+m

def c4free(edges,n):
    adj=[0]*n
    for a,b in edges:
        if a==b or adj[a]>>b&1:return False
        adj[a]|=1<<b;adj[b]|=1<<a
    return all((adj[a]&adj[b]).bit_count()<=1 for a in range(n) for b in range(a))

def local_shapes():
    shapes=collections.defaultdict(list);counts=collections.Counter()
    for i,j in itertools.permutations(range(1,5),2):
        k,l=sorted(set(range(1,5))-{i,j})
        attachment=[(10,2*i),(10,2*j+1),(11,2*i+1),(11,2*j),(12,2*k),(13,2*k+1),(14,2*l),(15,2*l+1)]
        for kind,vertices in [('internal_missing',[12,13,14,15]),('cross_missing',list(range(10,16)))]:
            for matching in matchings(vertices):
                if {tuple(sorted(e)) for e in matching}!={tuple(sorted((a^1,b^1))) for a,b in matching}:continue
                counts[kind+'_tested']+=1
                if not c4free(R+attachment+matching+[(16,u) for u in range(10,16)],17):continue
                shapes[kind].append(dict(attachment=attachment,internal=matching))
                counts[kind+'_survive']+=1
    return shapes,dict(counts)

def cross_matchings(kind):
    source=list(range(10 if kind=='internal_missing' else 12,16,2))
    target=list(range(16 if kind=='internal_missing' else 18,22,2))
    for perm in itertools.permutations(target):
        for bits in itertools.product(range(2),repeat=len(source)):
            yield [(a^t,b^(t^s)) for a,b,s in zip(source,perm,bits) for t in range(2)]

def run():
    started=time.monotonic();shapes,counts=local_shapes();out={}
    for kind,ss in shapes.items():
        tested=survived=0;first=None
        crosses=list(cross_matchings(kind))
        for left,right,cross in itertools.product(ss,ss,crosses):
            assert time.monotonic()-started<30,'30-second observation cap exceeded; incomplete'
            right_edges=[(a+6,b) for a,b in right['attachment']]+[(a+6,b+6) for a,b in right['internal']]
            edges=R+left['attachment']+left['internal']+right_edges+cross+[(22,u) for u in range(10,16)]+[(23,u) for u in range(16,22)]
            tested+=1
            if not c4free(edges,24):continue
            survived+=1
            if first is None:first=dict(left=left,right=right,cross=cross,edges=edges)
        out[kind]=dict(tested=tested,survived=survived,first_witness=first)
    return dict(status='COMPLETE',local_counts=counts,two_group_results=out,elapsed_seconds=time.monotonic()-started,scope='Induced residual plus two attached groups and their two nonadjacent centers only; not a full order-80 graph')
if __name__=='__main__':
    result=run();(ROOT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='two_group_results'}))
    print(json.dumps({k:{a:b for a,b in v.items() if a!='first_witness'} for k,v in result['two_group_results'].items()}))
