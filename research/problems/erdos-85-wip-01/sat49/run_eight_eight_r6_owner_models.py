#!/usr/bin/env python3
"""Enumerate and emit the r=6 eight-plus-eight owner CNFs.

The variable cross exterior-pair block is supported only on opposite-parity
pairs, has row and column sum two, and intertwines the two C8 adjacency
operators.  This script exhausts those finite constraints before emitting the
same exact-service/common-neighbor owner CNF used by the checked Lean models.
"""

from itertools import combinations, product
from pathlib import Path
import argparse


def cross_blocks():
    choices = []
    for x in range(8):
        odd = [y for y in range(8) if (y - x) % 2 == 1]
        choices.append([sum(1 << y for y in pair) for pair in combinations(odd, 2)])
    for rows in product(*choices):
        if any(sum((rows[x] >> y) & 1 for x in range(8)) != 2 for y in range(8)):
            continue
        if all(
            ((rows[(x - 1) % 8] >> y) & 1) + ((rows[(x + 1) % 8] >> y) & 1)
            == ((rows[x] >> ((y + 1) % 8)) & 1)
            + ((rows[x] >> ((y - 1) % 8)) & 1)
            for x in range(8)
            for y in range(8)
        ):
            yield rows


def ambient_adj(a, b):
    if (a < 8) != (b < 8):
        return False
    aa, bb = a % 8, b % 8
    return (aa - bb) % 8 in (1, 7)


def owners(rows):
    result = set()
    for base in (0, 8):
        for x in range(8):
            for d in (1, 3):
                result.add(tuple(sorted((base + x, base + (x + d) % 8))))
    for x, row in enumerate(rows):
        for y in range(8):
            if (row >> y) & 1:
                result.add((x, 8 + y))
    result = sorted(result)
    assert len(result) == 48
    return result


def owner_cnf(edges):
    vertices = range(16)
    target = [
        {v for v in vertices if not ambient_adj(a, v) and not ambient_adj(b, v)}
        for a, b in edges
    ]
    admissible = [
        (e, f)
        for e in range(48)
        for f in range(e + 1, 48)
        if set(edges[f]) <= target[e] and set(edges[e]) <= target[f]
    ]
    variable = {pair: i + 1 for i, pair in enumerate(admissible)}

    def lit(e, f):
        return variable[min(e, f), max(e, f)]

    clauses = []
    for e, (a, b) in enumerate(edges):
        for v in vertices:
            internal = int(ambient_adj(a, v)) + int(ambient_adj(b, v))
            terms = [
                lit(e, f)
                for f, pair in enumerate(edges)
                if f != e and v in pair and (min(e, f), max(e, f)) in variable
            ]
            if internal == 0:
                clauses.append(terms)
                clauses.extend([-terms[i], -terms[j]] for i in range(len(terms)) for j in range(i + 1, len(terms)))
            else:
                assert internal == 1
    for e in range(48):
        for f in range(e + 1, 48):
            capacity = 1 - len(set(edges[e]) & set(edges[f]))
            common = [
                k
                for k in range(48)
                if k not in (e, f)
                and (min(e, k), max(e, k)) in variable
                and (min(f, k), max(f, k)) in variable
            ]
            if capacity == 0:
                clauses.extend([-lit(e, k), -lit(f, k)] for k in common)
            else:
                clauses.extend(
                    [-lit(e, common[i]), -lit(f, common[i]), -lit(e, common[j]), -lit(f, common[j])]
                    for i in range(len(common))
                    for j in range(i + 1, len(common))
                )
    return len(variable), clauses


class Cnf:
    def __init__(self):
        self.ids = {}
        self.clauses = []

    def var(self, key):
        if key not in self.ids:
            self.ids[key] = len(self.ids) + 1
        return self.ids[key]

    def add(self, *clause):
        self.clauses.append(list(clause))


def combined_cnf(include_c4=True):
    """One CNF containing the cross-block variables and all owner clauses."""
    cnf = Cnf()
    vertices = range(16)
    fixed = set()
    for base in (0, 8):
        for x in range(8):
            for d in (1, 3):
                fixed.add(tuple(sorted((base + x, base + (x + d) % 8))))
    candidates = sorted(fixed | {(x, 8 + y) for x in range(8) for y in range(8) if (y - x) % 2})
    assert len(fixed) == 32 and len(candidates) == 64

    def active(e):
        edge = candidates[e]
        if edge in fixed:
            return None
        return cnf.var(("active", edge))

    def positive_active(e):
        a = active(e)
        return [] if a is None else [a]

    # Cross block: every row and column has exactly two active candidates.
    for shore in (0, 1):
        for z in range(8):
            es = [e for e, (x, y) in enumerate(candidates) if x < 8 <= y and (x if shore == 0 else y - 8) == z]
            vs = [active(e) for e in es]
            assert len(vs) == 4 and all(v is not None for v in vs)
            for triple in combinations(vs, 3):
                cnf.add(*triple)                 # at least two
                cnf.add(*(-v for v in triple))  # at most two

    def cross_var(x, y):
        edge = (x, 8 + y)
        if (y - x) % 2 == 0:
            return None
        return cnf.var(("active", edge))

    # Entrywise C8 intertwining: the two Boolean sums are equal.
    for x in range(8):
        for y in range(8):
            terms = [cross_var((x - 1) % 8, y), cross_var((x + 1) % 8, y),
                     cross_var(x, (y + 1) % 8), cross_var(x, (y - 1) % 8)]
            if all(v is None for v in terms):
                continue
            assert all(v is not None for v in terms)
            for bits in product((0, 1), repeat=4):
                if bits[0] + bits[1] != bits[2] + bits[3]:
                    cnf.add(*(v if bit == 0 else -v for v, bit in zip(terms, bits)))

    target = [
        {v for v in vertices if not ambient_adj(a, v) and not ambient_adj(b, v)}
        for a, b in candidates
    ]
    admissible = [
        (e, f)
        for e in range(64)
        for f in range(e + 1, 64)
        if set(candidates[f]) <= target[e] and set(candidates[e]) <= target[f]
    ]

    def hit(e, f):
        return cnf.var(("hit", min(e, f), max(e, f)))

    for e, f in admissible:
        h = hit(e, f)
        ae, af = active(e), active(f)
        if ae is not None:
            cnf.add(-h, ae)
        if af is not None:
            cnf.add(-h, af)

    # Each active owner's endpoint pair is served exactly once at every
    # remaining internal coordinate (internally or by an adjacent owner).
    for e, (a, b) in enumerate(candidates):
        ae = active(e)
        for v in vertices:
            internal = int(ambient_adj(a, v)) + int(ambient_adj(b, v))
            terms = [
                hit(e, f)
                for f, pair in enumerate(candidates)
                if f != e and v in pair and (min(e, f), max(e, f)) in admissible
            ]
            guard = [] if ae is None else [-ae]
            if internal == 0:
                cnf.add(*guard, *terms)
                for p, q in combinations(terms, 2):
                    cnf.add(-p, -q)
            else:
                assert internal == 1
                for p in terms:
                    cnf.add(*guard, -p)

    # Two active exterior owners have at most one common internal/exterior
    # neighbor.  Inactive candidates have no hits by the implications above.
    if include_c4:
        admissible_set = set(admissible)
        for e in range(64):
            for f in range(e + 1, 64):
                capacity = 1 - len(set(candidates[e]) & set(candidates[f]))
                common = [
                    k for k in range(64) if k not in (e, f)
                    and (min(e, k), max(e, k)) in admissible_set
                    and (min(f, k), max(f, k)) in admissible_set
                ]
                if capacity == 0:
                    for k in common:
                        cnf.add(-hit(e, k), -hit(f, k))
                else:
                    for k, ell in combinations(common, 2):
                        cnf.add(-hit(e, k), -hit(f, k), -hit(e, ell), -hit(f, ell))
    return cnf


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--combined", action="store_true")
    parser.add_argument("--no-c4", action="store_true")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.combined:
        cnf = combined_cnf(not args.no_c4)
        path = args.out / "eight_eight_r6_combined.cnf"
        with path.open("w") as stream:
            stream.write(f"p cnf {len(cnf.ids)} {len(cnf.clauses)}\n")
            for clause in cnf.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
        print("combined", len(cnf.ids), len(cnf.clauses), path)
        return
    blocks = list(cross_blocks())
    assert len(blocks) == 12
    for i, rows in enumerate(blocks):
        edge_list = owners(rows)
        variables, clauses = owner_cnf(edge_list)
        path = args.out / f"eight_eight_r6_{i:02}.cnf"
        with path.open("w") as stream:
            stream.write(f"p cnf {variables} {len(clauses)}\n")
            for clause in clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
        support = [[y for y in range(8) if (rows[x] >> y) & 1] for x in range(8)]
        print(i, variables, len(clauses), support)


if __name__ == "__main__":
    main()
