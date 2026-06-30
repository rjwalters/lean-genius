#!/usr/bin/env python3
"""
Durable verification cert for konigsberg-oq-04-oq-01 (S1 ORIENT).

OQ-04-OQ-01: "Can the Matrix Tree Theorem be formalized in Lean 4 using
Mathlib's linear algebra and determinant API, enabling a proof of the
arborescence count used by the BEST theorem (parent: konigsberg-oq-04)?"

This script independently re-derives the Matrix-Tree (Kirchhoff) counts that
the parent file proofs/Proofs/KonigsbergOQ04.lean asserts by hand, using only
the determinant of a Laplacian minor — i.e. it numerically validates the exact
statement that OQ-04 currently *axiomatizes* (KonigsbergOQ04.lean:83-84,
"Axiomatized because the proof requires the Matrix Tree Theorem").

Two halves:
  (A) DIRECTED Matrix-Tree (Tutte): number of in-arborescences rooted at r
      = (r,r) cofactor of L_out = diag(d_out) - A, where A[u][v] = #arcs u->v.
      Reproduces the parent file's arborescenceCount values:
          C3 (triDigraph) rooted at A -> 1   (triArb is unique; tri_best_consistent)
          K3 (k3Digraph)  rooted at A -> 3   (k3Arb1/2/3; k3_arb_complete)
      This is the version the BEST theorem actually needs.

  (B) UNDIRECTED Matrix-Tree (Kirchhoff): tau(G) = any cofactor of L = D - A.
      This is the version closest to Mathlib's existing
      Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean (SimpleGraph.lapMatrix).
      Checked against standard closed forms (Cayley n^(n-2), cycle = n, etc).

No external deps beyond the stdlib (exact integer Bareiss determinant), so the
cert is reproducible in the Docker-free / blackout environment.
"""

from fractions import Fraction
from itertools import combinations, product


def det_int(mat):
    """Exact determinant of an integer matrix via fraction-free elimination."""
    n = len(mat)
    if n == 0:
        return 1
    M = [[Fraction(x) for x in row] for row in mat]
    sign = 1
    for k in range(n):
        if M[k][k] == 0:
            swap = next((r for r in range(k + 1, n) if M[r][k] != 0), None)
            if swap is None:
                return 0
            M[k], M[swap] = M[swap], M[k]
            sign = -sign
        for i in range(k + 1, n):
            factor = M[i][k] / M[k][k]
            for j in range(k, n):
                M[i][j] -= factor * M[k][j]
    d = Fraction(sign)
    for i in range(n):
        d *= M[i][i]
    assert d.denominator == 1, f"non-integer det {d}"
    return d.numerator


def delete_row_col(mat, idx):
    return [[mat[i][j] for j in range(len(mat)) if j != idx]
            for i in range(len(mat)) if i != idx]


# ---------------------------------------------------------------------------
# (A) DIRECTED Matrix-Tree (Tutte): in-arborescences rooted at r.
# ---------------------------------------------------------------------------
def in_arborescence_count(n, arcs, root):
    """arcs: list of (u,v) directed u->v. Vertices 0..n-1.
    Count spanning in-trees (every vertex has a directed path TO root)."""
    A = [[0] * n for _ in range(n)]
    for (u, v) in arcs:
        assert u != v, "loopless digraph expected"
        A[u][v] += 1
    dout = [sum(A[v]) for v in range(n)]            # out-degree = row sum
    L = [[(dout[i] if i == j else 0) - A[i][j] for j in range(n)] for i in range(n)]
    return det_int(delete_row_col(L, root))


def brute_in_arborescences(n, arcs, root):
    """Ground-truth: enumerate all parent-functions giving a valid in-tree."""
    arcset = set(arcs)
    count = 0
    others = [v for v in range(n) if v != root]
    # each non-root vertex picks exactly one out-arc to its parent
    for choice in product(*[[(v, w) for (a, w) in arcs if a == v] for v in others]):
        parent = {root: root}
        ok = True
        for (v, w) in choice:
            parent[v] = w
        if len(parent) != n:
            ok = False
        # validity: every vertex reaches root by following parent (no cycle)
        if ok:
            for v in range(n):
                seen, cur = set(), v
                while cur != root:
                    if cur in seen:
                        ok = False
                        break
                    seen.add(cur)
                    cur = parent[cur]
                if not ok:
                    break
        if ok:
            count += 1
    return count


# ---------------------------------------------------------------------------
# (B) UNDIRECTED Matrix-Tree (Kirchhoff): tau(G) = any cofactor of L = D - A.
# ---------------------------------------------------------------------------
def spanning_tree_count(n, edges):
    A = [[0] * n for _ in range(n)]
    for (u, v) in edges:
        A[u][v] += 1
        A[v][u] += 1
    deg = [sum(A[i]) for i in range(n)]
    L = [[(deg[i] if i == j else 0) - A[i][j] for j in range(n)] for i in range(n)]
    cof0 = det_int(delete_row_col(L, 0))
    # cofactor independence: deleting any other row/col gives the same value
    for r in range(1, n):
        assert det_int(delete_row_col(L, r)) == cof0, "cofactor not independent of r"
    return cof0


def brute_spanning_trees(n, edges):
    """Ground-truth: count edge-subsets of size n-1 that are acyclic+connected."""
    if n == 1:
        return 1
    count = 0
    for subset in combinations(edges, n - 1):
        parent = list(range(n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        acyclic = True
        for (u, v) in subset:
            ru, rv = find(u), find(v)
            if ru == rv:
                acyclic = False
                break
            parent[ru] = rv
        if acyclic and len({find(i) for i in range(n)}) == 1:
            count += 1
    return count


def main():
    A_, B_, C_ = 0, 1, 2
    failures = []

    print("=== (A) DIRECTED Matrix-Tree: in-arborescences (BEST-relevant) ===")
    # C3 = triDigraph: A->B, B->C, C->A. Root A. Lean: triArb unique -> 1.
    c3_arcs = [(A_, B_), (B_, C_), (C_, A_)]
    c3 = in_arborescence_count(3, c3_arcs, A_)
    c3_bf = brute_in_arborescences(3, c3_arcs, A_)
    print(f"C3 (triDigraph) rooted at A: cofactor={c3}, brute={c3_bf}, "
          f"Lean arborescenceCount=1")
    failures += [] if c3 == 1 == c3_bf else ["C3 directed"]

    # K3 = k3Digraph: all 6 arcs. Root A. Lean: k3Arb1/2/3, k3_arb_complete -> 3.
    k3_arcs = [(A_, B_), (A_, C_), (B_, A_), (B_, C_), (C_, A_), (C_, B_)]
    k3 = in_arborescence_count(3, k3_arcs, A_)
    k3_bf = brute_in_arborescences(3, k3_arcs, A_)
    print(f"K3 (k3Digraph)  rooted at A: cofactor={k3}, brute={k3_bf}, "
          f"Lean arborescenceCount=3")
    failures += [] if k3 == 3 == k3_bf else ["K3 directed"]

    # Root-independence sanity for the balanced K3 (all roots give 3).
    for r in (A_, B_, C_):
        v = in_arborescence_count(3, k3_arcs, r)
        failures += [] if v == 3 else [f"K3 root {r}"]

    print("\n=== (B) UNDIRECTED Matrix-Tree: Kirchhoff spanning-tree count ===")
    cases = [
        ("P3 path 0-1-2", 3, [(0, 1), (1, 2)], 1),
        ("K3 triangle", 3, [(0, 1), (1, 2), (0, 2)], 3),
        ("C4 cycle", 4, [(0, 1), (1, 2), (2, 3), (0, 3)], 4),
        ("K4 (Cayley 4^2)", 4,
         [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 16),
        ("K5 (Cayley 5^3)", 5,
         [(i, j) for i in range(5) for j in range(i + 1, 5)], 125),
    ]
    for name, n, edges, expected in cases:
        tau = spanning_tree_count(n, edges)
        bf = brute_spanning_trees(n, edges)
        print(f"{name:18s}: cofactor={tau:4d}, brute={bf:4d}, expected={expected}")
        failures += [] if tau == expected == bf else [name]

    print("\n=== RESULT ===")
    if failures:
        print("FAIL:", failures)
        raise SystemExit(1)
    print("All Matrix-Tree (directed + undirected) checks PASS.")
    print("The arborescence counts axiomatized in KonigsbergOQ04.lean are")
    print("reproduced by a single Laplacian-minor determinant.")


if __name__ == "__main__":
    main()
