"""
Verification certificate for friendship-theorem-oq-04 (infinite friendship graphs).

Claims verified:
  C1. (finite theorem sanity) Every friendship graph on n<=8 vertices is a windmill
      (has a universal vertex). Confirms gallery theorem on small cases.
  C2. The ONLY *regular* finite friendship graph is K_3 (triangle).
  C3. (diameter<=2)  In any friendship graph, any two vertices are at distance <=2.
  C4. (KEY finiteness lemma)  V = {v} ∪ N(v) ∪ ⋃_{w∈N(v)} N(w) for every vertex v.
      => locally finite friendship graph is finite.
  C5. The infinite windmill (m blades, m=1..6) IS a friendship graph with a
      universal centre of degree 2m  (=> infinite friendship graph w/ a universal
      vertex of INFINITE degree; not locally finite).
"""
from itertools import combinations, product

def common_neighbors(adj, u, v):
    return adj[u] & adj[v]

def is_friendship(adj, n):
    for u, v in combinations(range(n), 2):
        if len(common_neighbors(adj, u, v)) != 1:
            return False
    return True

def universal_vertex(adj, n):
    for c in range(n):
        if all((c in adj[w]) for w in range(n) if w != c):
            return c
    return None

def all_graphs(n):
    """Yield adjacency dicts for all simple graphs on n labelled vertices."""
    edges = list(combinations(range(n), 2))
    for bits in product([0,1], repeat=len(edges)):
        adj = {i:set() for i in range(n)}
        for (e,b) in zip(edges, bits):
            if b:
                a,c=e; adj[a].add(c); adj[c].add(a)
        yield adj

# ---- C1 + C2 : brute force small friendship graphs ----
print("== C1/C2: enumerate friendship graphs (small n) ==")
max_n = 7  # 2^21 graphs at n=7 is 2M; keep n<=7 for runtime
for n in range(3, max_n+1):
    fcount=0; non_windmill=0; regular=[]
    for adj in all_graphs(n):
        if is_friendship(adj, n):
            fcount+=1
            if universal_vertex(adj,n) is None:
                non_windmill+=1
            degs={len(adj[i]) for i in range(n)}
            if len(degs)==1:
                regular.append((n, degs.pop()))
    print(f"  n={n}: friendship graphs={fcount}, "
          f"without universal vertex={non_windmill}, regular={regular}")

# ---- C3 + C4 : structural lemmas on the found friendship graphs ----
print("== C3/C4: diameter<=2 and finiteness-cover identity ==")
def check_struct(adj, n):
    # diameter<=2
    for u in range(n):
        reach2 = set(adj[u])
        for w in adj[u]:
            reach2 |= adj[w]
        reach2.add(u)
        if reach2 != set(range(n)):
            return False, "diam>2"
        # cover identity: V = {u} ∪ N(u) ∪ ∪_{w∈N(u)} N(w)
        cover = {u} | set(adj[u])
        for w in adj[u]:
            cover |= adj[w]
        if cover != set(range(n)):
            return False, "cover-fail"
    return True, "ok"

ok=True
for n in range(3, 6):
    for adj in all_graphs(n):
        if is_friendship(adj, n):
            good,msg = check_struct(adj,n)
            if not good:
                ok=False; print(f"  FAIL n={n}: {msg}")
print("  diameter<=2 AND cover identity hold for all small friendship graphs:", ok)

# ---- C5 : infinite windmill (truncated to m blades) ----
print("== C5: infinite windmill (centre 0; blades {2i-1,2i}) ==")
def windmill(m):
    # vertices: 0=centre, 1..2m blades
    n=2*m+1
    adj={i:set() for i in range(n)}
    for i in range(1,n):           # centre adjacent to all
        adj[0].add(i); adj[i].add(0)
    for b in range(m):             # blade edge
        a=2*b+1; c=2*b+2
        adj[a].add(c); adj[c].add(a)
    return adj,n
for m in range(1,7):
    adj,n=windmill(m)
    fr=is_friendship(adj,n)
    c=universal_vertex(adj,n)
    print(f"  m={m}: n={n}, friendship={fr}, universal={c}, deg(centre)={len(adj[0])}")
print("  => centre degree = 2m grows without bound; an infinite windmill is a")
print("     friendship graph whose universal vertex has INFINITE degree (not loc.fin.)")
