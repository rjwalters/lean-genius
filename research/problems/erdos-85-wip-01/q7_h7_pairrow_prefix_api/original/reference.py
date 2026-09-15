"""Optimistic pair-row domains for a valid a7 partial-host graph.

Caller supplies the accepted a7 fixed-high graph plus a legal host prefix.
future_host_possible may overapproximate, but must never omit a legal future host.
At a full host prefix it must be False for every currently unhosted pair.
"""
import itertools

def rows(adjacency, vertex, future_host_possible):
    g=list(map(set,adjacency))
    assert len(g)==49 and 21<=vertex<42
    H=set(range(7)); E=set(range(42,49)); A=set(range(7,42))
    support=[ns&H for ns in g]
    assert len(support[vertex])==2 and not g[vertex]&A
    hosted=len(g[vertex]&E)
    assert hosted in (0,1) and len(g[vertex])==2+hosted
    sizes={4} if hosted else ({4,5} if future_host_possible else {5})
    eligible=[v for v in sorted(A) if v!=vertex and v not in g[vertex]
              and all(not g[v]&g[w] for w in g[vertex])]
    result=set()
    # Increasing-vertex traversal, separate from the native colour-first DFS.
    def visit(start,chosen,used):
        if used==H:
            if len(chosen) in sizes: result.add(sum(1<<v for v in chosen))
            return
        if len(chosen)>=max(sizes): return
        for i in range(start,len(eligible)):
            v=eligible[i]
            if support[v]&used or any(g[v]&g[w] for w in chosen): continue
            visit(i+1,chosen+[v],used|support[v])
    visit(0,[],set())
    return result

def future_possible(options,order,depth,vertex):
    """Sound overapproximation; intentionally ignores conflicts between options."""
    return any(any(mask>>vertex&1 for mask in options[i]) for i in order[depth:])
