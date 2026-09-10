"""Bounded H7 empty-to-singleton/pair incidence search; no full graph claim."""
import argparse
import itertools
import json
from pathlib import Path
import time

PAIRS=list(itertools.combinations(range(7),2))


def matchings(size):
    return [tuple(indices) for indices in itertools.combinations(range(21),size)
            if len({v for i in indices for v in PAIRS[i]})==2*size]


OPTIONS={d:matchings(d) for d in range(4)}


def verify(empty_edges, pair_hosts, singleton_hosts):
    # Vertices H=0..6,E=7..13,S=14..27,P=28..48.
    edges=[(7+u,7+v) for u,v in empty_edges]
    edges += [(c,14+2*c+k) for c in range(7) for k in range(2)]
    edges += [(c,28+i) for i,pair in enumerate(PAIRS) for c in pair]
    edges += [(7+host,28+i) for i,host in enumerate(pair_hosts) if host is not None]
    edges += [(7+host,14+i) for i,hosts in enumerate(singleton_hosts) for host in hosts]
    adj=[set() for _ in range(49)]
    for u,v in edges:
        assert u!=v and v not in adj[u]
        adj[u].add(v);adj[v].add(u)
    assert all(len(adj[v])==8 for v in range(7))
    assert all(len(adj[v])==7 for v in range(7,14))
    assert all(len(adj[u]&adj[v])<=1 for u,v in itertools.combinations(range(49),2))
    return sorted([list(sorted(e)) for e in edges])


def search(row, cap, seconds):
    edges=[tuple(e) for e in row['edges']]
    adj=[set() for _ in range(7)]
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    order=sorted(range(7),key=lambda v:(-len(adj[v]),v))
    pair_hosts=[None]*21;singletons=[[] for _ in range(14)]
    shared=set();nodes=0;started=time.monotonic();answer=None
    class Limit(Exception):pass
    def tick():
        nonlocal nodes
        nodes+=1
        if nodes>cap or time.monotonic()-started>seconds:raise Limit
    def visit(depth):
        nonlocal answer
        tick()
        if depth==7:
            answer=dict(pair_hosts=list(pair_hosts),singleton_hosts=[list(s) for s in singletons])
            answer['partial_edges']=verify(edges,pair_hosts,singletons)
            return True
        v=order[depth];d=len(adj[v])
        choices=OPTIONS[d]
        if depth==0:
            # A global high-label permutation normalizes this first matching.
            choices=[tuple(PAIRS.index((2*i,2*i+1)) for i in range(d))]
        for matching in choices:
            if any(pair_hosts[i] is not None for i in matching):continue
            colors={c for i in matching for c in PAIRS[i]}
            singles=[c for c in range(7) if c not in colors]
            for i in matching:pair_hosts[i]=v
            def assign(k):
                tick()
                if k==len(singles):return visit(depth+1)
                color=singles[k]
                for copy in range(2):
                    slot=2*color+copy;hosts=singletons[slot]
                    # The twin singleton names are interchangeable until used.
                    if copy==1 and not singletons[2*color] and not hosts:continue
                    if len(hosts)>=2:continue
                    pair=None
                    if hosts:
                        u=hosts[0];pair=tuple(sorted((u,v)))
                        if adj[u]&adj[v] or pair in shared:continue
                    hosts.append(v)
                    if pair is not None:shared.add(pair)
                    if assign(k+1):return True
                    if pair is not None:shared.remove(pair)
                    hosts.pop()
                return False
            if assign(0):return True
            for i in matching:pair_hosts[i]=None
        return False
    try:
        found=visit(0);status='PARTIAL_WITNESS' if found else 'INCIDENCE_EXHAUSTED'
    except Limit:status='UNKNOWN_AT_CAP'
    return dict(mask=row['mask'],a=row['a'],status=status,nodes=nodes,seconds=time.monotonic()-started,
                witness=answer,empty_edges=edges)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--cap',type=int,default=100000)
    ap.add_argument('--seconds',type=float,default=3);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    source=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_universal_singleton_capacity.json')
    rows=[r for r in json.loads(source.read_text()) if not r['excluded']]
    assert len(rows)==28
    results=[]
    for row in rows:
        result=search(row,args.cap,args.seconds);results.append(result)
        print(json.dumps({k:v for k,v in result.items() if k not in ('witness','empty_edges')}),flush=True)
    output=dict(scope='Empty-to-S/P incidence only; high and empty degrees/C4 verified, remaining low degrees and S/P edges not completed',
                cap=args.cap,seconds_per_case=args.seconds,results=results)
    with args.output.open('x') as out:json.dump(output,out,indent=2)


if __name__=='__main__':main()
