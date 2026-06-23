#!/usr/bin/env python3
"""
Durable verification for Erdős Problem #574 (OQ-01), case k = 2.

Conjecture:  ex(n; {C_{2k-1}, C_{2k}}) = (1 + o(1)) * (n/2)^{1+1/k}  for k >= 2.

The genuinely OPEN part of the conjecture is the upper bound (and even
ex(n; C_{2k})'s exact constant is open for general k). The LOWER bound,
however, transfers for free from the C_{2k}-alone extremal construction
for one structural reason:

    The standard extremal C_{2k}-free graphs (incidence graphs of
    generalized k-gons / projective planes) are BIPARTITE, hence have NO
    odd cycles at all, hence are automatically C_{2k-1}-free.

So the lower bound ex(n; {C_{2k-1}, C_{2k}}) >= (bipartite construction
count) is UNCONDITIONAL — "forbidding C_{2k-1} is free" on the lower-bound
side.

This script demonstrates that fact concretely for k = 2 (forbid C_3 and
C_4) using the point-line incidence graph of the projective plane PG(2,q)
over GF(q), q prime. For each q it checks:

  1. The graph is bipartite (points vs lines)  => no odd cycle  => C_3-free.
  2. The graph is genuinely C_3-free (direct triangle search).
  3. The graph is C_4-free (direct 4-cycle search; girth = 6).
  4. Edge count e ~ (n/2)^{3/2} = (n/2)^{1+1/2}, matching the conjecture.

A graph that is simultaneously C_3-free AND C_4-free with ~(n/2)^{3/2}
edges is exactly a lower-bound witness for ex(n; {C_3, C_4}).
"""

from itertools import combinations


def projective_points(q):
    """Representatives of 1-dim subspaces of GF(q)^3 (q prime), i.e. the
    points of PG(2,q). Normalize so the first nonzero coordinate is 1."""
    pts = []
    for x in range(q):
        for y in range(q):
            for z in range(q):
                if (x, y, z) == (0, 0, 0):
                    continue
                # find first nonzero coordinate, require it == 1 (canonical rep)
                v = (x, y, z)
                lead = next(c for c in v if c != 0)
                inv = pow(lead, q - 2, q)  # inverse in GF(q), q prime
                canon = tuple((c * inv) % q for c in v)
                if canon == v:
                    pts.append(v)
    return pts


def incidence_graph(q):
    """Bipartite point-line incidence graph of PG(2,q).
    Points and lines are the same set of representatives (duality);
    point p is incident to line L iff the dot product p.L == 0 mod q."""
    reps = projective_points(q)
    # vertices: ('P', i) for points, ('L', j) for lines
    points = [('P', i) for i in range(len(reps))]
    lines = [('L', j) for j in range(len(reps))]
    adj = {v: set() for v in points + lines}
    for i, p in enumerate(reps):
        for j, L in enumerate(reps):
            dot = (p[0] * L[0] + p[1] * L[1] + p[2] * L[2]) % q
            if dot == 0:
                adj[('P', i)].add(('L', j))
                adj[('L', j)].add(('P', i))
    return adj, reps


def is_bipartite_PL(adj):
    """The construction is bipartite by design (P-side vs L-side). Verify
    no edge stays within a side."""
    for u, nbrs in adj.items():
        for v in nbrs:
            if u[0] == v[0]:
                return False
    return True


def has_triangle(adj):
    verts = list(adj)
    for a, b, c in combinations(verts, 3):
        if b in adj[a] and c in adj[b] and a in adj[c]:
            return True
    return False


def has_c4(adj):
    """C_4 exists iff some pair of vertices has >= 2 common neighbours."""
    verts = list(adj)
    for u, w in combinations(verts, 2):
        common = adj[u] & adj[w]
        if len(common) >= 2:
            return True
    return False


def edge_count(adj):
    return sum(len(n) for n in adj.values()) // 2


def run():
    print(f"{'q':>3} {'n':>5} {'edges':>6} {'bipart':>7} {'C3free':>7} "
          f"{'C4free':>7} {'(n/2)^1.5':>10} {'ratio':>7}")
    print("-" * 62)
    all_ok = True
    for q in (2, 3, 5, 7):
        adj, reps = incidence_graph(q)
        n = len(adj)
        e = edge_count(adj)
        bip = is_bipartite_PL(adj)
        c3free = not has_triangle(adj)
        c4free = not has_c4(adj)
        target = (n / 2) ** 1.5
        ratio = e / target
        # sanity: PG(2,q) has q^2+q+1 points & lines, each (q+1)-regular,
        # edges = (q+1)(q^2+q+1).
        npts = q * q + q + 1
        assert len(reps) == npts, (len(reps), npts)
        assert n == 2 * npts
        assert e == (q + 1) * npts
        ok = bip and c3free and c4free
        all_ok = all_ok and ok
        print(f"{q:>3} {n:>5} {e:>6} {str(bip):>7} {str(c3free):>7} "
              f"{str(c4free):>7} {target:>10.2f} {ratio:>7.4f}")

    print("-" * 62)
    print("Structural facts confirmed for k = 2:")
    print("  * incidence graph of PG(2,q) is bipartite -> no odd cycle")
    print("    -> C_3-free WITHOUT any extra work (this is the 'free' part)")
    print("  * also C_4-free (girth 6), so {C_3,C_4}-free")
    print("  * edges = (q+1)(q^2+q+1) ~ (n/2)^{3/2}, ratio -> 1 as q grows")
    print("  => unconditional lower bound ex(n;{C_3,C_4}) >= ~(n/2)^{3/2}")
    print()
    print("ALL CHECKS PASSED" if all_ok else "FAILURE")
    return all_ok


if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
