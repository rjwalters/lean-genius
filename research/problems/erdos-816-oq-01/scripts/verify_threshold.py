#!/usr/bin/env python3
"""
Erdos #816 OQ-01: "Remove the n >= 600 restriction from Chen-Ma's stronger result."

Chen-Ma (2025) stronger result:
    For n >= 600, every graph G on 2n+1 vertices with >= n^2 + n edges contains
    two vertices of EQUAL DEGREE joined by a PATH OF LENGTH 3 (P3 = 4 distinct
    vertices v0-v1-v2-v3, three edges), EXCEPT the complete bipartite K_{n,n+1}.

OQ: can the threshold n >= 600 be lowered (ideally removed)?

This script brute-forces small n to locate counterexamples: graphs that are
  (a) on 2n+1 vertices, (b) have >= n^2 + n edges, (c) are NOT K_{n,n+1},
  (d) but contain NO equal-degree pair joined by a path of length 3.
Any such graph is a genuine obstruction to lowering the threshold to that n.

Build-free; pure-Python (host python3). No external deps.
"""

from itertools import combinations
import sys


def all_pairs(N):
    return list(combinations(range(N), 2))


def degrees(adj, N):
    return [len(adj[v]) for v in range(N)]


def has_p3(adj, u, v):
    """Path of length 3 u-a-b-v with u,a,b,v pairwise distinct."""
    for a in adj[u]:
        if a == v:
            continue
        for b in adj[a]:
            if b == u or b == v or b == a:
                continue
            if v in adj[b]:
                return True
    return False


def has_equal_degree_p3_pair(adj, N):
    deg = degrees(adj, N)
    for u in range(N):
        for v in range(u + 1, N):
            if deg[u] == deg[v] and has_p3(adj, u, v):
                return True
    return False


def is_complete_bipartite_n_np1(adj, N, n):
    """Is the graph K_{n,n+1}? Detect via: bipartite with parts sizes {n,n+1}
    and ALL cross edges present, no intra-part edges. We test by checking the
    graph equals the complement of (K_n disjoint-union K_{n+1}) for some split,
    using the degree fingerprint then verifying. Robust small-N check."""
    deg = degrees(adj, N)
    # K_{n,n+1}: n vertices of degree n+1, (n+1) vertices of degree n.
    cnt_np1 = sum(1 for d in deg if d == n + 1)
    cnt_n = sum(1 for d in deg if d == n)
    if not (cnt_np1 == n and cnt_n == n + 1):
        return False
    A = [v for v in range(N) if deg[v] == n + 1]   # size n
    B = [v for v in range(N) if deg[v] == n]        # size n+1
    Aset, Bset = set(A), set(B)
    # every A-B pair adjacent, no A-A or B-B edge
    for a in A:
        if adj[a] != Bset:
            return False
    for b in B:
        if adj[b] != Aset:
            return False
    return True


def adj_from_edges(edges, N):
    adj = [set() for _ in range(N)]
    for (x, y) in edges:
        adj[x].add(y)
        adj[y].add(x)
    return adj


def canonical(adj, N):
    """Cheap canonical form by brute permutation (only used for small N)."""
    from itertools import permutations
    best = None
    base = [(x, y) for x in range(N) for y in adj[x] if x < y]
    for p in permutations(range(N)):
        e = frozenset(frozenset((p[x], p[y])) for (x, y) in base)
        key = tuple(sorted(tuple(sorted(s)) for s in e))
        if best is None or key < best:
            best = key
    return best


def scan(n, full_canonical=False, cap=None):
    N = 2 * n + 1
    min_edges = n * n + n
    pairs = all_pairs(N)
    M = len(pairs)
    print(f"--- n={n}: N={N} vertices, threshold edges >= {min_edges}, "
          f"max edges {M} ---")
    counterexamples = []  # graphs failing the property, NOT K_{n,n+1}
    k23_count = 0
    checked = 0
    for k in range(min_edges, M + 1):
        for combo in combinations(range(M), k):
            checked += 1
            if cap and checked > cap:
                print(f"    [CAP reached at {cap} graphs; partial result]")
                return counterexamples, checked, True
            edges = [pairs[i] for i in combo]
            adj = adj_from_edges(edges, N)
            if has_equal_degree_p3_pair(adj, N):
                continue
            # graph LACKS the property
            if is_complete_bipartite_n_np1(adj, N, n):
                k23_count += 1
                continue
            counterexamples.append(adj)
    print(f"    graphs checked: {checked}")
    print(f"    K_(n,n+1) instances lacking property: {k23_count} "
          f"(expected: the K_(n,n+1) exception)")
    # dedupe counterexamples up to isomorphism if requested
    if full_canonical and counterexamples:
        seen = {}
        for adj in counterexamples:
            c = canonical(adj, N)
            if c not in seen:
                seen[c] = adj
        reps = list(seen.values())
        print(f"    NON-K(n,n+1) counterexamples: {len(counterexamples)} labelled, "
              f"{len(reps)} up to isomorphism")
        for adj in reps:
            eds = sorted((x, y) for x in range(N) for y in adj[x] if x < y)
            print(f"      deg={sorted(degrees(adj, N))}  |E|={len(eds)}  edges={eds}")
        return reps, checked, False
    else:
        print(f"    NON-K(n,n+1) counterexamples: {len(counterexamples)} (labelled)")
        if counterexamples:
            # show degree sequences (cheap, no canonicalization)
            from collections import Counter
            ds = Counter(tuple(sorted(degrees(a, N))) for a in counterexamples)
            for seq, c in sorted(ds.items()):
                print(f"      degseq={list(seq)}  x{c} labelled graphs")
        return counterexamples, checked, False


def rigorous_n1():
    """n=1: 2n+1 = 3 vertices < 4, so NO graph admits any path of length 3.
    Hence hasEqualDegreePath3Pair is FALSE for EVERY 3-vertex graph. Any graph
    with >= n^2+n = 2 edges that is not K_{1,2} is a counterexample, e.g. the
    triangle K_3 (3 edges). No computation needed."""
    print("--- n=1: N=3 vertices, threshold edges >= 2 ---")
    print("    A path of length 3 requires 4 distinct vertices; N=3 < 4.")
    print("    => NO 3-vertex graph has an equal-degree P3 pair.")
    print("    Triangle K_3 (3 >= 2 edges) is NOT K_{1,2} and lacks the property.")
    print("    => n=1 is a genuine non-K(n,n+1) counterexample (restriction "
          "cannot reach n=1).")


if __name__ == "__main__":
    rigorous_n1()
    print()
    scan(2, full_canonical=True)
    print()
    # n=3 is heavier (~1.05M graphs with >= 12 edges). Early-exit makes dense
    # graphs cheap. Pass a cap via argv to bound runtime under CPU contention.
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else None
    scan(3, full_canonical=False, cap=cap)
    print()
    print("Interpretation: a NON-K(n,n+1) counterexample at a given n proves the")
    print("threshold cannot be lowered to that n. Absence (n>=2 small) is")
    print("consistent with K_{n,n+1} being the unique exception and the n>=600")
    print("bound being an artifact of Chen-Ma's proof method, not the truth.")
