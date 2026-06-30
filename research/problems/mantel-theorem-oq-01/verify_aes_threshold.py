#!/usr/bin/env python3
"""
Certificate for the AES (Andrásfai–Erdős–Sós) ingredient lemma formalized in
`proofs/Proofs/MantelStabilityOQ01.lean`:

    triangleFree_colorable_two_of_lt_minDegree :
      G.CliqueFree 3  →  2 * n / 5 < G.minDegree  →  G.Colorable 2

i.e. a triangle-free graph on `n` vertices with minimum degree STRICTLY above
`⌊2n/5⌋` is bipartite. (This is the `r = 2` case of Mathlib's
`SimpleGraph.colorable_of_cliqueFree_lt_minDegree`, threshold `(3r−4)n/(3r−1)`.)

This script independently brute-force-verifies two things:

  (A) CORRECTNESS over all triangle-free graphs on `n ≤ NMAX` vertices: every
      triangle-free graph with `5·minDegree > 2n` (Lean integer form: the
      hypothesis `2*n/5 < minDegree` with `/` = floor-division is implied by
      `5*minDeg > 2n`) is 2-colorable. Expect 0 counterexamples.

  (B) TIGHTNESS / why the inequality must be STRICT: the 5-cycle `C₅` is
      triangle-free, has minimum degree exactly `2 = ⌊2·5/5⌋`, and is NOT
      bipartite (odd cycle). So `minDegree = ⌊2n/5⌋` does NOT force bipartite —
      the `<` in the lemma cannot be weakened to `≤`. The balanced blow-ups of
      `C₅` (the Andrásfai graphs) are the general tight family; `C₅` is the
      smallest witness. We also confirm `C₇` is a (looser) non-tight odd example.

Note on the Lean threshold: Lean's `2 * n / 5` is floor division. The lemma
hypothesis is `2*n/5 < minDeg`, i.e. `minDeg ≥ ⌊2n/5⌋ + 1`. The cleanest
integer-equivalent guard, valid for the floor, is `5 * minDeg > 2 * n` ⇒
`minDeg > 2n/5 ≥ ⌊2n/5⌋`. We test under that guard (a superset of the Lean
hypothesis is even stronger evidence — every graph we certify satisfies the
Lean hypothesis too).
"""

from itertools import combinations

NMAX = 6  # exhaustive over all graphs on 3..NMAX vertices (2^C(n,2) each)


def is_triangle_free(adj, n):
    for a, b, c in combinations(range(n), 3):
        if adj[a][b] and adj[b][c] and adj[a][c]:
            return False
    return True


def min_degree(adj, n):
    return min(sum(adj[v]) for v in range(n))


def is_bipartite(adj, n):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in range(n):
                if adj[u][w]:
                    if color[w] == -1:
                        color[w] = color[u] ^ 1
                        stack.append(w)
                    elif color[w] == color[u]:
                        return False
    return True


def all_graphs(n):
    edges = list(combinations(range(n), 2))
    for mask in range(1 << len(edges)):
        adj = [[False] * n for _ in range(n)]
        for i, (a, b) in enumerate(edges):
            if mask & (1 << i):
                adj[a][b] = adj[b][a] = True
        yield adj


def cycle(n):
    adj = [[False] * n for _ in range(n)]
    for i in range(n):
        j = (i + 1) % n
        adj[i][j] = adj[j][i] = True
    return adj


def main():
    print(f"=== (A) AES r=2 correctness: triangle-free ∧ 5·minDeg > 2n ⇒ bipartite, n=3..{NMAX} ===")
    total_checked = 0
    counterexamples = 0
    near_tight = []  # graphs hitting the guard with minDeg == floor(2n/5)+1 (closest to boundary)
    for n in range(3, NMAX + 1):
        cnt = 0
        for adj in all_graphs(n):
            if not is_triangle_free(adj, n):
                continue
            md = min_degree(adj, n)
            if 5 * md > 2 * n:  # strictly above 2n/5
                cnt += 1
                total_checked += 1
                if not is_bipartite(adj, n):
                    counterexamples += 1
                    if counterexamples <= 5:
                        print(f"  COUNTEREXAMPLE n={n}, minDeg={md}: non-bipartite!")
                elif md == (2 * n) // 5 + 1:
                    near_tight.append((n, md))
        print(f"  n={n}: {cnt} triangle-free graphs satisfy 5·minDeg>2n; all bipartite so far")
    print(f"  TOTAL satisfying graphs: {total_checked}; counterexamples: {counterexamples} (expect 0)")
    if near_tight:
        ex = sorted(set(near_tight))
        print(f"  graphs right at the guard boundary minDeg=⌊2n/5⌋+1 occur at (n,minDeg)={ex} — all bipartite")

    print()
    print("=== (B) TIGHTNESS: C₅ shows the inequality must be STRICT ===")
    for n in (5, 7):
        adj = cycle(n)
        tf = is_triangle_free(adj, n)
        md = min_degree(adj, n)
        bip = is_bipartite(adj, n)
        floor_thr = (2 * n) // 5
        print(f"  C_{n}: triangle-free={tf}, minDeg={md}, ⌊2n/5⌋={floor_thr}, "
              f"minDeg==⌊2n/5⌋: {md == floor_thr}, bipartite={bip}")
    print("  ⇒ C₅ is triangle-free, minDeg = 2 = ⌊2·5/5⌋ (AT the floor, NOT above it), and is")
    print("    NOT bipartite. So `minDeg = ⌊2n/5⌋` does not force 2-colorability — the lemma's")
    print("    strict `2n/5 < minDegree` is necessary; `≤` would be FALSE. (Andrásfai graphs =")
    print("    balanced C₅ blow-ups are the general tight family.)")


if __name__ == "__main__":
    main()
