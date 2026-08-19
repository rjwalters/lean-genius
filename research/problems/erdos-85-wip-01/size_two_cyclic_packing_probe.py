#!/usr/bin/env python3
"""Probe the abstract SIZE-TWO-EIGENLINE cyclic packing code.

This intentionally forgets the exterior graph and retains exactly the data in
`SizeTwoCyclicFullPermutationCode`: correlated two-hole partial permutations,
cross-agreement at most one, reciprocity, and looplessness.  SAT means those
axioms alone do not refute the grid; UNSAT gives a small model from which to
mine a uniform packing proof.
"""

from __future__ import annotations

import argparse
from itertools import product
import subprocess
import tempfile

import z3


class Cnf:
    """Tiny direct CNF builder for the finite packing constraints."""

    def __init__(self) -> None:
        self.ids: dict[tuple[int, int, int, int], int] = {}
        self.clauses: list[list[int]] = []

    def var(self, key: tuple[int, int, int, int]) -> int:
        if key not in self.ids:
            self.ids[key] = len(self.ids) + 1
        return self.ids[key]

    def exactly_one(self, variables: list[int]) -> None:
        self.clauses.append(variables)
        for i, left in enumerate(variables):
            for right in variables[i + 1:]:
                self.clauses.append([-left, -right])


def build_cnf(
    q: int,
    a: int,
    *,
    cross_mode: str = "full",
    agreement_ts: set[int] | None = None,
    agreement_ds: set[int] | None = None,
    reciprocity: bool = True,
    loopless: bool = True,
) -> Cnf:
    """Boolean one-hot encoding, avoiding Z3's integer arithmetic overhead."""
    ts = allowed_differences(q, a)
    columns = [c for c in range(q) if c not in {0, q - 1}]
    rows = {t: admissible_rows(q, t) for t in ts}
    cnf = Cnf()

    def choices(x: int, t: int, r: int) -> list[int]:
        return [cnf.var((x, t, r, c)) for c in columns]

    for x, t in product(range(q), ts):
        for r in rows[t]:
            cnf.exactly_one(choices(x, t, r))
        for c in columns:
            cnf.exactly_one([cnf.var((x, t, r, c)) for r in rows[t]])

    if reciprocity:
        for x, t in product(range(q), ts):
            for r in rows[t]:
                for c in columns:
                    source = cnf.var((x, t, r, c))
                    s = (c - r) % q
                    reverse_row = (-r) % q
                    reverse_column = (t - r) % q
                    if (s not in rows or reverse_row not in rows[s]
                            or reverse_column not in columns):
                        cnf.clauses.append([-source])
                    else:
                        reverse = cnf.var(
                            ((x + r) % q, s, reverse_row, reverse_column)
                        )
                        cnf.clauses.append([-source, reverse])
                    if loopless and r == 0 and c == t:
                        cnf.clauses.append([-source])

    # An agreement at row r is a conjunction of two one-hot choices.  To say
    # at most one row agrees, forbid every pair of such conjunctions directly.
    for x, d, t, u in product(range(q), range(q), ts, ts):
        if d == 0 and t == u:
            continue
        if cross_mode == "same-t" and t != u:
            continue
        if cross_mode == "same-x" and d != 0:
            continue
        if cross_mode == "none":
            continue
        if agreement_ts is not None and t not in agreement_ts:
            continue
        if agreement_ds is not None and d not in agreement_ds:
            continue
        possible: list[tuple[int, list[tuple[int, int]]]] = []
        for r in rows[t]:
            shifted = (r - d) % q
            if shifted not in rows[u]:
                continue
            witnesses = []
            for c in columns:
                shifted_column = (c - d) % q
                if shifted_column in columns:
                    witnesses.append((
                        cnf.var((x, t, r, c)),
                        cnf.var(((x + d) % q, u, shifted, shifted_column)),
                    ))
            possible.append((r, witnesses))
        for i, (_, left_witnesses) in enumerate(possible):
            for _, right_witnesses in possible[i + 1:]:
                for left_a, left_b in left_witnesses:
                    for right_a, right_b in right_witnesses:
                        cnf.clauses.append(
                            [-left_a, -left_b, -right_a, -right_b]
                        )
    return cnf


def solve_with_kissat(cnf: Cnf) -> str:
    with tempfile.NamedTemporaryFile(mode="w", suffix=".cnf") as dimacs:
        dimacs.write(f"p cnf {len(cnf.ids)} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            dimacs.write(" ".join(map(str, clause)) + " 0\n")
        dimacs.flush()
        result = subprocess.run(
            ["kissat", "--quiet", dimacs.name], capture_output=True, text=True
        )
    if result.returncode == 10:
        return "sat"
    if result.returncode == 20:
        return "unsat"
    raise RuntimeError(result.stderr or result.stdout)


def allowed_differences(q: int, a: int) -> list[int]:
    return [t for t in range(q) if t not in {a % q, (-1 - a) % q}]


def admissible_rows(q: int, t: int) -> list[int]:
    return [r for r in range(q) if t != r and t != (r - 1) % q]


def build(
    q: int,
    a: int,
    *,
    cross_mode: str = "full",
    agreement_ts: set[int] | None = None,
    agreement_ds: set[int] | None = None,
    reciprocity: bool = True,
    loopless: bool = True,
) -> tuple[z3.Solver, dict[tuple[int, int, int], z3.IntNumRef]]:
    ts = allowed_differences(q, a)
    columns = [c for c in range(q) if c not in {0, q - 1}]
    rows = {t: admissible_rows(q, t) for t in ts}
    solver = z3.Solver()
    p: dict[tuple[int, int, int], z3.IntNumRef] = {}

    # Each (x,t) is a bijection from its q-2 admissible rows to the fixed
    # q-2 admissible columns.
    for x, t in product(range(q), ts):
        entries = []
        for r in rows[t]:
            v = z3.Int(f"p_{x}_{t}_{r}")
            p[x, t, r] = v
            solver.add(z3.Or([v == c for c in columns]))
            entries.append(v)
        solver.add(z3.Distinct(entries))

    # Cross-source/cross-difference agreement: after translating both the
    # source row and target column, distinct codewords share at most one edge.
    for x, d, t, u in product(range(q), range(q), ts, ts):
        if d == 0 and t == u:
            continue
        if cross_mode == "same-t" and t != u:
            continue
        if cross_mode == "same-x" and d != 0:
            continue
        if cross_mode == "none":
            continue
        if agreement_ts is not None and t not in agreement_ts:
            continue
        if agreement_ds is not None and d not in agreement_ds:
            continue
        agreements = []
        for r in rows[t]:
            shifted = (r - d) % q
            if shifted in rows[u]:
                agreements.append(
                    z3.If(p[x, t, r] == (d + p[(x + d) % q, u, shifted]) % q, 1, 0)
                )
        solver.add(z3.Sum(agreements) <= 1)

    # Reciprocity.  The target difference is s = column-row.  Reversing the
    # routed edge starts at x+r in difference s and row -r, and returns t-r.
    if reciprocity:
        for x, t in product(range(q), ts):
            for r in rows[t]:
                c = p[x, t, r]
                cases = []
                for s in ts:
                    reverse_row = (-r) % q
                    if reverse_row not in rows[s]:
                        continue
                    cases.append(
                        z3.And(
                            c == (r + s) % q,
                            p[(x + r) % q, s, reverse_row] == (t - r) % q,
                        )
                    )
                solver.add(z3.Or(cases))
                if loopless and r == 0:
                    solver.add(c != t)

    return solver, p


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int)
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--backend", choices=["z3", "kissat"], default="z3")
    parser.add_argument(
        "--cross-mode", choices=["full", "same-t", "same-x", "none"], default="full"
    )
    parser.add_argument("--no-reciprocity", action="store_true")
    parser.add_argument("--no-loopless", action="store_true")
    parser.add_argument(
        "--agreement-t", type=int, action="append",
        help="retain agreement constraints only for these source differences",
    )
    parser.add_argument(
        "--agreement-d", type=int, action="append",
        help="retain agreement constraints only for these nonzero source shifts",
    )
    args = parser.parse_args()
    candidates = [args.a] if args.a is not None else range(1, args.q - 1)
    for a in candidates:
        if a % args.q in {0, args.q - 1}:
            continue
        build_args = dict(
            cross_mode=args.cross_mode,
            agreement_ts=None if args.agreement_t is None else
                {t % args.q for t in args.agreement_t},
            agreement_ds=None if args.agreement_d is None else
                {d % args.q for d in args.agreement_d},
            reciprocity=not args.no_reciprocity,
            loopless=not args.no_loopless,
        )
        if args.backend == "kissat":
            result = solve_with_kissat(build_cnf(args.q, a, **build_args))
            print(f"q={args.q} a={a % args.q}: {result}")
            if result == "sat":
                break
            continue
        solver, p = build(args.q, a, **build_args)
        solver.set(timeout=args.timeout_ms)
        result = solver.check()
        print(f"q={args.q} a={a % args.q}: {result}")
        if result == z3.sat:
            model = solver.model()
            ts = allowed_differences(args.q, a)
            for x in range(args.q):
                for t in ts:
                    values = [(r, model.eval(p[x, t, r]).as_long()) for r in admissible_rows(args.q, t)]
                    print(f"  x={x} t={t}: {values}")
            break


if __name__ == "__main__":
    main()
