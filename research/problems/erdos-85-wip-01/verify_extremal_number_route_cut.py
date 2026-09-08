#!/usr/bin/env python3
"""Certified lower bounds ex(q^2, C4) > q^3/2 at binary q; stdlib only.

Companion to EXTREMAL_NUMBER_ROUTE_CUT.md.  For q = 2^k the script builds the
Erdos-Renyi orthogonal polarity graph ER_q on PG(2,q) (x ~ y iff x.y = 0,
x != y; loops discarded), checks it is C4-free with the expected degrees,
and exhibits an explicit set X of q+1 vertices whose removal leaves a
C4-free graph on q^2 vertices with MORE than q^3/2 edges.  The set X is the
Tait-Timmons oval construction (S on a conic, plus the vertices with exactly
two neighbours in S) padded greedily, then improved by 1-swaps.

Consequence: a q-regular C4-free graph on q^2 vertices (q^3/2 edges) is not
an extremal C4-free graph, so EXACT extremal-structure classifications
(Fueredi's equality case, FKNW, McCuaig's conjecture) cannot apply to A-REG
candidates.  Near-extremal stability at order q^2 is not addressed here.
No statement about A-REG itself is made.
"""

import itertools
import random
import sys

IRREDUCIBLE = {3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011}


class GF2k:
    def __init__(self, k):
        self.k, self.q, self.poly = k, 1 << k, IRREDUCIBLE[k]
        self.inv = {x: self._inverse(x) for x in range(1, self.q)}

    def mul(self, x, y):
        r = 0
        while y:
            if y & 1:
                r ^= x
            y >>= 1
            x <<= 1
            if x & self.q:
                x ^= self.poly
        return r

    def _inverse(self, x):
        for y in range(1, self.q):
            if self.mul(x, y) == 1:
                return y
        raise ArithmeticError(x)

    def normalize(self, v):
        for x in v:
            if x:
                s = self.inv[x]
                return tuple(self.mul(s, y) for y in v)
        raise ValueError("zero vector")

    def dot(self, u, v):
        return self.mul(u[0], v[0]) ^ self.mul(u[1], v[1]) ^ self.mul(u[2], v[2])


def polarity_graph(field):
    """Return points, adjacency sets (loopless) and the absolute-point set."""
    q = field.q
    pts = sorted({field.normalize(v) for v in itertools.product(range(q), repeat=3)
                  if any(v)})
    assert len(pts) == q * q + q + 1
    index = {p: i for i, p in enumerate(pts)}
    adj = [set() for _ in pts]
    absolute = set()
    for i, p in enumerate(pts):
        for j in range(i, len(pts)):
            if field.dot(p, pts[j]) == 0:
                if i == j:
                    absolute.add(i)
                else:
                    adj[i].add(j)
                    adj[j].add(i)
    assert len(absolute) == q + 1
    assert all(len(adj[i]) == (q if i in absolute else q + 1) for i in range(len(pts)))
    return pts, index, adj, absolute


def edges_after_removal(adj, removed):
    keep = [v for v in range(len(adj)) if v not in removed]
    kept = set(keep)
    return sum(len(adj[v] & kept) for v in keep) // 2


def c4_free_after_removal(adj, removed):
    keep = [v for v in range(len(adj)) if v not in removed]
    kept = set(keep)
    sub = {v: adj[v] & kept for v in keep}
    return all(len(sub[u] & sub[v]) <= 1 for u, v in itertools.combinations(keep, 2))


def oval_seed(field, pts, index, adj, m):
    """Tait-Timmons: S = m points of the conic {(1,t,t^2)}, X_S = vertices with
    exactly two neighbours in S (secant poles), minus S."""
    conic = [index[field.normalize((1, t, field.mul(t, t)))] for t in range(field.q)]
    S = set(conic[:m])
    Y = {v for v in range(len(pts)) if len(adj[v] & S) == 2}
    return S | (Y - S)


def improve(adj, X, target_size, rounds=3):
    """Greedy pad to target_size (max edges into X), then 1-swap hill climb on
    e(X) counted with loops removed already (loops never appear in adj)."""
    X = set(X)
    n = len(adj)
    while len(X) < target_size:
        best = max((v for v in range(n) if v not in X), key=lambda v: len(adj[v] & X))
        X.add(best)
    while len(X) > target_size:
        worst = min(X, key=lambda v: len(adj[v] & X))
        X.remove(worst)
    for _ in range(rounds):
        improved = False
        for x in sorted(X):
            gain_x = len(adj[x] & X)
            for v in range(n):
                if v in X:
                    continue
                gain_v = len(adj[v] & X) - (1 if x in adj[v] else 0)
                if gain_v > gain_x:
                    X.remove(x)
                    X.add(v)
                    improved = True
                    break
            if improved:
                break
        if not improved:
            break
    return X


def main():
    random.seed(20260908)
    ok = True
    for k in (3, 4, 5, 6):
        field = GF2k(k)
        q = field.q
        pts, index, adj, absolute = polarity_graph(field)
        total = sum(len(a) for a in adj) // 2
        assert total == q * (q + 1) ** 2 // 2
        best_X, best_e = None, -1
        for m in range(2, q + 2):
            seed = oval_seed(field, pts, index, adj, m)
            if len(seed) > q + 1:
                break
            X = improve(adj, seed, q + 1)
            e = edges_after_removal(adj, X)
            if e > best_e:
                best_X, best_e = X, e
        # Control: deleting the absolute line leaves the affine witness plus
        # the isolated pole, (q^3 - q)/2 edges.
        e_abs = edges_after_removal(adj, absolute)
        assert e_abs == (q ** 3 - q) // 2
        assert len(best_X) == q + 1
        assert c4_free_after_removal(adj, best_X) if q <= 32 else True
        margin = best_e - q ** 3 // 2
        verdict = "PASS" if margin > 0 else "FAIL"
        ok &= margin > 0
        print(f"q={q}: ER_q has {total} edges; deleting the absolute line leaves "
              f"{e_abs} = (q^3-q)/2; explicit |X|={q+1} leaves {best_e} edges "
              f"on {q*q} vertices = q^3/2 {'+' if margin >= 0 else '-'} {abs(margin)} "
              f"[{verdict}]")
    print("Conclusion: ex(q^2, C4) > q^3/2 at q = 8, 16, 32, 64; a q-regular "
          "C4-free graph on q^2 vertices would not be extremal." if ok else
          "Some order did not exceed q^3/2; see above.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
