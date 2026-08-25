#!/usr/bin/env python3
"""Emit the honest 88-owner CNF for the mu=-3, (0,5) endpoint.

The older Lean generator reused the 80-owner h114 universe and omitted the
four antipodal exterior edges on each C8 shore.  Here each shore contributes
eight offset-1/3 edges and four offset-4 edges, followed by all 64 guarded
cross owners.  Variables 1..64 are cross-defect entries; hit variables start
at 65 in lexicographic admissible-owner-pair order.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path


Clause = list[int]
Owner = tuple[int, int]


def g_adj(x: int, y: int) -> bool:
    return (x < 8) == (y < 8) and (x - y) % 8 in (1, 7)


def sign(sigma: int, x: int) -> int:
    return x % 2 if x < 8 else (x % 8 + sigma) % 2


def owners(u_tri: bool, v_tri: bool) -> list[Owner]:
    def shore(base: int, tri: bool) -> list[Owner]:
        offset = 1 if tri else 3
        ordinary = [tuple(sorted((base + i, base + (i + offset) % 8)))
                    for i in range(8)]
        antipodal = [(base + i, base + i + 4) for i in range(4)]
        return ordinary + antipodal

    return (shore(0, u_tri) + shore(8, v_tri) +
            [(i, 8 + j) for i in range(8) for j in range(8)])


def pair_mem(p: Owner, w: int) -> bool:
    return w in p


def served(p: Owner) -> list[int]:
    adjacent = g_adj(*p)
    return [w for w in range(16)
            if g_adj(p[0], w) or g_adj(p[1], w) or
            (adjacent and pair_mem(p, w))]


def twelve(p: Owner) -> list[int]:
    s = set(served(p))
    adjacent = g_adj(*p)
    return [w for w in range(16)
            if w not in s and not (adjacent and pair_mem(p, w))]


def admissible(p: Owner, q: Owner) -> bool:
    tp, tq = set(twelve(p)), set(twelve(q))
    return p != q and q[0] in tp and q[1] in tp and p[0] in tq and p[1] in tq


def dvar(i: int, j: int) -> int:
    return i * 8 + j + 1


def hit_pairs(os: list[Owner]) -> list[tuple[int, int]]:
    return [(a, b) for a in range(len(os)) for b in range(a + 1, len(os))
            if admissible(os[a], os[b])]


def exactly_two(xs: list[int]) -> list[Clause]:
    assert len(xs) == 4
    return [[y for y in xs if y != x] for x in xs] + [
        [-xs[i], -xs[j], -xs[k]]
        for i in range(4) for j in range(i + 1, 4)
        for k in range(j + 1, 4)
    ]


def exactly_three(xs: list[int]) -> list[Clause]:
    assert len(xs) == 4
    return ([[xs[i], xs[j]] for i in range(4) for j in range(i + 1, 4)] +
            [[-x for x in xs]])


def cross_degree_clauses(sigma: int) -> list[Clause]:
    out: list[Clause] = []
    for i in range(8):
        same = [dvar(i, j) for j in range(8) if sign(sigma, i) == sign(sigma, 8 + j)]
        opp = [dvar(i, j) for j in range(8) if sign(sigma, i) != sign(sigma, 8 + j)]
        out += exactly_two(same) + exactly_three(opp)
    for j in range(8):
        same = [dvar(i, j) for i in range(8) if sign(sigma, i) == sign(sigma, 8 + j)]
        opp = [dvar(i, j) for i in range(8) if sign(sigma, i) != sign(sigma, 8 + j)]
        out += exactly_two(same) + exactly_three(opp)
    return out


def sum_eq(a: int, b: int, c: int, d: int) -> list[Clause]:
    return [[-a, c, d], [-b, c, d], [-c, a, b], [-d, a, b],
            [-a, -b, c], [-a, -b, d], [-c, -d, a], [-c, -d, b]]


def intertwine_clauses() -> list[Clause]:
    out: list[Clause] = []
    for i in range(8):
        for j in range(8):
            out += sum_eq(dvar((i - 1) % 8, j), dvar((i + 1) % 8, j),
                          dvar(i, (j + 1) % 8), dvar(i, (j - 1) % 8))
    return out


def guard(p: Owner) -> int | None:
    return dvar(p[0], p[1] - 8) if p[0] < 8 <= p[1] else None


def generate(u_tri: bool, v_tri: bool, sigma: int) -> tuple[list[Clause], int, int]:
    os = owners(u_tri, v_tri)
    pairs = hit_pairs(os)
    xvar = {p: 65 + k for k, p in enumerate(pairs)}

    def x(a: int, b: int) -> int | None:
        return xvar.get(tuple(sorted((a, b))))

    clauses = cross_degree_clauses(sigma) + intertwine_clauses()

    for a, b in pairs:
        xv = x(a, b)
        assert xv is not None
        for o in (a, b):
            g = guard(os[o])
            if g is not None:
                clauses.append([-xv, -g])

    for a, p in enumerate(os):
        prefix = [guard(p)] if guard(p) is not None else []
        for w in twelve(p):
            lits = [x(a, b) for b, q in enumerate(os)
                    if b != a and pair_mem(q, w) and x(a, b) is not None]
            hits = [lit for lit in lits if lit is not None]
            clauses.append(prefix + hits)
            for i in range(len(hits)):
                for j in range(i + 1, len(hits)):
                    clauses.append(prefix + [-hits[i], -hits[j]])

    for a in range(len(os)):
        for b in range(a + 1, len(os)):
            common = [g for g in range(len(os))
                      if g not in (a, b) and x(a, g) is not None and x(b, g) is not None]
            if set(os[a]) & set(os[b]):
                clauses += [[-x(a, g), -x(b, g)] for g in common]  # type: ignore[list-item]
            else:
                for gi in range(len(common)):
                    for hi in range(gi + 1, len(common)):
                        g, h = common[gi], common[hi]
                        clauses.append([-x(a, g), -x(b, g), -x(a, h), -x(b, h)])  # type: ignore[list-item]

    max_var = 64 + len(pairs)
    assert len(os) == 88 and len(set(os)) == 88
    assert all(c and all(lit != 0 for lit in c) for c in clauses)
    return clauses, max_var, len(pairs)


def dimacs_bytes(clauses: list[Clause], max_var: int) -> bytes:
    lines = [f"p cnf {max_var} {len(clauses)}"]
    lines += [" ".join(map(str, clause)) + " 0" for clause in clauses]
    return ("\n".join(lines) + "\n").encode()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--u-mode", choices=("tri", "tf"), required=True)
    parser.add_argument("--v-mode", choices=("tri", "tf"), required=True)
    parser.add_argument("--sigma", type=int, choices=(0, 1), required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    clauses, max_var, pair_count = generate(
        args.u_mode == "tri", args.v_mode == "tri", args.sigma)
    payload = dimacs_bytes(clauses, max_var)
    args.output.write_bytes(payload)
    digest = hashlib.sha256(payload).hexdigest()
    print(f"owners=88 hit_pairs={pair_count} vars={max_var} clauses={len(clauses)} "
          f"sha256={digest} output={args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
