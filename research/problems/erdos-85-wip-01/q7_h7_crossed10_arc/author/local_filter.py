"""Necessary local-row filter for a COMPLETE high0 host assignment, before guest edges.

This is not a full graph completion test. A feasible return means only that each
outside vertex separately has a legal completed row. UNKNOWN must never prune.
Indices0..6 are high vertices; all other vertices are low. No author-name mapping
is needed. The caller can share a deadline and a node tick with a larger search.
"""
import time

def check_host_assignment(adjacency, *, max_nodes=100000, deadline=None,
                          all_omissions=False, validate=True, external_tick=None):
    g=[set(ns) for ns in adjacency]
    if len(g)!=49:raise ValueError('expected49vertices')
    H=sorted(g[0]);outside=sorted(set(range(7,49))-set(H));hi=set(range(7))
    if len(H)!=8 or len(outside)!=34:raise ValueError('not an H7 host partition')
    masks=[sum(1<<c for c in ns if c<7) for ns in g]
    groups=[sorted(g[h]&set(outside)) for h in H]
    host={u:next((h for h in H if u in g[h]),None) for u in outside}
    if validate:
        assert all(v!=u and u in g[v] for u in range(49) for v in g[u])
        assert all(len(g[c])==8 for c in hi)
        assert all(len(g[u]&g[v])<=1 for u in range(49) for v in range(u))
        assert all(len(g[h])==7 and len(g[h]&set(H))==1 for h in H)
        assert all(host[u] is not None and g[u]-hi=={host[u]} for u in outside), 'guest edges must not yet be assigned'
    mate={h:next(iter(g[h]&set(H))) for h in H}
    allowed={u:[i for i,h in enumerate(H) if h!=mate[host[u]] and not(masks[u]&masks[h]&126)] for u in outside}
    def legal(u,v):return u!=v and v not in g[u] and all(not(g[v]&g[w]) for w in g[u])
    nodes=0;rows=[]
    def tick():
        nonlocal nodes
        nodes+=1
        if nodes>max_nodes or (deadline is not None and time.monotonic()>deadline):raise TimeoutError
        if external_tick is not None:external_tick()
    def dfs(todo,covered,selected,missing,domains):
        tick()
        if not todo:return selected if covered==missing else None
        choices=[]
        for i in todo:
            vs=[v for v in domains[i] if not masks[v]&covered and all(not(g[v]&g[w]) for w in selected)]
            if not vs:return None
            choices.append((len(vs),i,vs))
        possible=covered
        for _,i,vs in choices:
            for v in vs:possible|=masks[v]
        if possible!=missing:return None
        _,i,vs=min(choices)
        for v in vs:
            found=dfs([j for j in todo if j!=i],covered|masks[v],selected+[v],missing,domains)
            if found is not None:return found
        return None
    try:
        for u in outside:
            missing=127^masks[host[u]]
            domains={i:[v for v in groups[i] if legal(u,v) and masks[v]&~missing==0] for i in allowed[u]}
            feasible=[];witness=None
            for omit in allowed[u]:
                keep=[i for i in allowed[u] if i!=omit]
                assert len(keep)==6-masks[u].bit_count()
                found=dfs(keep,0,[],missing,domains)
                if found is not None:
                    feasible.append(omit);witness=found
                    if not all_omissions:break
            rows.append({'vertex':u,'feasible_omissions':feasible,'witness':witness})
            if not feasible:return {'status':'INFEASIBLE','vertex':u,'nodes':nodes,'rows':rows}
        return {'status':'LOCAL_FEASIBLE','nodes':nodes,'rows':rows}
    except TimeoutError:
        return {'status':'UNKNOWN','nodes':nodes,'rows':rows}
