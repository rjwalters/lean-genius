#!/usr/bin/env python3
"""Emit the all-triangle C10+C6 per-cell D-system as deterministic DIMACS.

This is the one-fiber (size six in every row and column) specialization of
`percell_D_fibers_z3.py`.  In this specialization the colour predicates are
tautological: every occupied cell has the unique colour, and the two holes in
each row/column already force the required six occupied cells.  The remaining
variables are the 64 K-holes and one symmetric D-variable for every diagonal
pair of cells.
"""

from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path


N = 8


def make_cycle(xs, ys):
    return [z for pair in zip((('x', x) for x in xs), (('y', y) for y in ys)) for z in pair]


def cycle_edges(cycle):
    result = set()
    for i, a in enumerate(cycle):
        b = cycle[(i + 1) % len(cycle)]
        result.add((a[1], b[1]) if a[0] == 'x' else (b[1], a[1]))
    return result


class Cnf:
    def __init__(self):
        self.names = {}
        self.clauses = []

    def var(self, name):
        if name not in self.names:
            self.names[name] = len(self.names) + 1
        return self.names[name]

    def add(self, *lits):
        self.clauses.append(tuple(lits))

    def guarded_exactly(self, guard, lits, target):
        """Add `guard -> sum(lits) = target`; guard is a list of literals."""
        prefix = tuple(-lit for lit in guard)
        if target < 0 or target > len(lits):
            self.clauses.append(prefix)
            return
        # At most target.
        for subset in combinations(lits, target + 1):
            self.clauses.append(prefix + tuple(-lit for lit in subset))
        # At least target.
        for subset in combinations(lits, len(lits) - target + 1):
            self.clauses.append(prefix + tuple(subset))

    def exactly(self, lits, target):
        self.guarded_exactly([], lits, target)

    def write(self, path):
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('w') as stream:
            stream.write('c all-triangle C10+C6 per-cell D-system\n')
            for name, number in self.names.items():
                stream.write(f'c var {number} {name}\n')
            stream.write(f'p cnf {len(self.names)} {len(self.clauses)}\n')
            for clause in self.clauses:
                stream.write(' '.join(map(str, clause)) + ' 0\n')


def build():
    cycles = [make_cycle(range(5), range(5)), make_cycle(range(5, 8), range(5, 8))]
    h_edges = set().union(*(cycle_edges(cycle) for cycle in cycles))
    nhx = {x: {y for a, y in h_edges if a == x} for x in range(N)}
    nhy = {y: {x for x, b in h_edges if b == y} for y in range(N)}
    sx = lambda a, b: len(nhx[a] & nhx[b])
    sy = lambda a, b: len(nhy[a] & nhy[b])

    cnf = Cnf()
    hole = {(x, y): cnf.var(f'K_{x}_{y}') for x in range(N) for y in range(N)}
    cells = list(hole)
    dvar = {}
    for a, b in combinations(cells, 2):
        if a[0] == b[0] or a[1] == b[1]:
            continue
        d = cnf.var(f'D_{a[0]}{a[1]}_{b[0]}{b[1]}')
        dvar[(a, b)] = d
        cnf.add(-d, -hole[a])
        cnf.add(-d, -hole[b])

    def d(a, b):
        return dvar[(a, b) if a < b else (b, a)]

    # K is a two-factor disjoint from H.
    for edge in sorted(h_edges):
        cnf.add(-hole[edge])
    for x in range(N):
        cnf.exactly([hole[(x, y)] for y in range(N)], 2)
    for y in range(N):
        cnf.exactly([hole[(x, y)] for x in range(N)], 2)

    # Exact per-cell row and column D counts.  A positive hole literal means
    # the cell is absent; D laws are imposed only when the root is occupied.
    for x, y in cells:
        for xp in range(N):
            if xp == x:
                continue
            ds = [d((x, y), (xp, yy)) for yy in range(N) if yy != y]
            base = 2 - sx(x, xp)
            cnf.guarded_exactly([-hole[(x, y)], hole[(xp, y)]], ds, base)
            cnf.guarded_exactly([-hole[(x, y)], -hole[(xp, y)]], ds, base - 1)
        for yp in range(N):
            if yp == y:
                continue
            ds = [d((x, y), (xx, yp)) for xx in range(N) if xx != x]
            base = 2 - sy(y, yp)
            cnf.guarded_exactly([-hole[(x, y)], hole[(x, yp)]], ds, base)
            cnf.guarded_exactly([-hole[(x, y)], -hole[(x, yp)]], ds, base - 1)
    return cnf


def main():
    parser = ArgumentParser()
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    cnf = build()
    cnf.write(args.output)
    print(f'variables={len(cnf.names)} clauses={len(cnf.clauses)} output={args.output}')


if __name__ == '__main__':
    main()
