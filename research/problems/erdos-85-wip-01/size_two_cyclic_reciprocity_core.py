#!/usr/bin/env python3
"""Extract tracked UNSAT cores for the reduced cyclic packing model.

The bijection constraints are permanent.  Each same-difference agreement
bound and each individual reciprocity route is guarded by an assumption, so
Z3 can report which translated-source pairs and reverse darts are actually
needed for the q=6 contradiction.  A deletion pass greedily shrinks that core.
"""

from __future__ import annotations

import argparse
from itertools import product

import z3


def allowed_differences(q: int, a: int) -> list[int]:
    return [t for t in range(q) if t not in {a % q, (-1 - a) % q}]


def admissible_rows(q: int, t: int) -> list[int]:
    return [r for r in range(q) if t != r and t != (r - 1) % q]


def build(
    q: int, a: int, granularity: str
) -> tuple[z3.Solver, list[z3.BoolRef]]:
    ts = allowed_differences(q, a)
    columns = [c for c in range(q) if c not in {0, q - 1}]
    rows = {t: admissible_rows(q, t) for t in ts}
    solver = z3.Solver()
    p: dict[tuple[int, int, int], z3.IntNumRef] = {}

    for x, t in product(range(q), ts):
        entries = []
        for r in rows[t]:
            value = z3.Int(f"p_{x}_{t}_{r}")
            p[x, t, r] = value
            solver.add(z3.Or([value == c for c in columns]))
            entries.append(value)
        solver.add(z3.Distinct(entries))

    assumption_by_name: dict[str, z3.BoolRef] = {}

    def guard(kind: str, x: int, d: int | None, t: int, r: int | None) -> z3.BoolRef:
        if granularity == "family":
            name = f"{kind}_t{t}"
        elif granularity == "base":
            name = f"{kind}_x{x}_t{t}"
        elif kind == "A":
            name = f"A_x{x}_d{d}_t{t}"
        else:
            name = f"R_x{x}_t{t}_r{r}"
        return assumption_by_name.setdefault(name, z3.Bool(name))

    # Guard each same-difference agreement constraint separately.
    for x, d, t in product(range(q), range(1, q), ts):
        constraint_guard = guard("A", x, d, t, None)
        agreements = []
        for r in rows[t]:
            shifted = (r - d) % q
            if shifted in rows[t]:
                agreements.append(
                    z3.If(
                        p[x, t, r]
                        == (d + p[(x + d) % q, t, shifted]) % q,
                        1,
                        0,
                    )
                )
        solver.add(z3.Implies(constraint_guard, z3.Sum(agreements) <= 1))

    # Guard each forward route's reciprocity disjunction separately.
    for x, t in product(range(q), ts):
        for r in rows[t]:
            constraint_guard = guard("R", x, None, t, r)
            column = p[x, t, r]
            reverse_cases = []
            for s in ts:
                reverse_row = (-r) % q
                if reverse_row not in rows[s]:
                    continue
                reverse_cases.append(
                    z3.And(
                        column == (r + s) % q,
                        p[(x + r) % q, s, reverse_row] == (t - r) % q,
                    )
                )
            solver.add(z3.Implies(constraint_guard, z3.Or(reverse_cases)))

    return solver, list(assumption_by_name.values())


def greedy_minimize(
    solver: z3.Solver,
    all_guards: list[z3.BoolRef],
    core: list[z3.BoolRef],
    timeout_ms: int,
) -> list[z3.BoolRef]:
    kept = list(core)
    index = 0
    while index < len(kept):
        trial = kept[:index] + kept[index + 1 :]
        trial_names = {str(item) for item in trial}
        solver.push()
        solver.add([
            guard if str(guard) in trial_names else z3.Not(guard)
            for guard in all_guards
        ])
        solver.set(timeout=timeout_ms)
        result = solver.check()
        solver.pop()
        if result == z3.unsat:
            kept = trial
            index = 0
        else:
            index += 1
    return kept


def summarize(core: list[z3.BoolRef]) -> None:
    agreement = [str(g) for g in core if str(g).startswith("A_")]
    reciprocity = [str(g) for g in core if str(g).startswith("R_")]
    print(f"core_size={len(core)} agreement={len(agreement)} reciprocity={len(reciprocity)}")
    print("agreement guards:")
    for name in agreement:
        print(f"  {name}")
    print("reciprocity guards:")
    for name in reciprocity:
        print(f"  {name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q", type=int, default=6)
    parser.add_argument("--a", type=int, default=1)
    parser.add_argument("--timeout-ms", type=int, default=60_000)
    parser.add_argument("--minimize", action="store_true")
    parser.add_argument(
        "--granularity", choices=["family", "base", "route"], default="family"
    )
    parser.add_argument(
        "--disable", action="append", default=[], help="guard name to force false"
    )
    args = parser.parse_args()

    solver, assumptions = build(args.q, args.a, args.granularity)
    disabled = set(args.disable)
    solver.add([
        z3.Not(guard) if str(guard) in disabled else guard
        for guard in assumptions
    ])
    solver.set(timeout=args.timeout_ms)
    result = solver.check()
    print(f"q={args.q} a={args.a % args.q}: {result}")
    if result != z3.unsat:
        return
    core = list(assumptions)
    print("initial ", end="")
    summarize(core)
    if args.minimize:
        # Rebuild without the permanent all-true assignments for deletion.
        solver, assumptions = build(args.q, args.a, args.granularity)
        core = greedy_minimize(solver, assumptions, core, args.timeout_ms)
        print("minimized ", end="")
        summarize(core)


if __name__ == "__main__":
    main()
