#!/usr/bin/env python3
"""Exact near-orthomorphism model of the first positive-variance stratum.

This is equivalent to the cap-free/full-base-dependent edge model under
``--minimal-block-variance``, but it uses one local permutation of q-2
symbols per cell rather than one Boolean per ordered cell pair.
"""

from __future__ import annotations

import argparse

import z3


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--directed", action="store_true")
    parser.add_argument("--reciprocity-core", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    args = parser.parse_args()
    if args.directed and args.reciprocity_core:
        parser.error("--directed and --reciprocity-core are incompatible")

    q = args.q
    holes = {args.a % q, (-1 - args.a) % q}
    differences = tuple(t for t in range(q) if t not in holes)
    residues = tuple(r for r in range(q) if r not in {0, 1})
    residue_set = set(residues)
    cells = tuple((x, t) for x in range(q) for t in differences)

    psi = {
        (x, t, r): z3.Int(f"psi_{x}_{t}_{r}")
        for x, t in cells for r in residues
    }
    solver = z3.Solver()

    # Each cell carries a permutation psi_p of R.
    for x, t in cells:
        values = [psi[x, t, r] for r in residues]
        for value in values:
            solver.add(z3.Or([value == s for s in residues]))
        solver.add(z3.Distinct(values))

        # The target fibre u=-t-r-psi_p(r) has one missing and one doubled
        # value, with all other allowed values occurring once.
        loads = []
        for u in differences:
            load = z3.Sum([
                z3.If(((-t - r - psi[x, t, r]) % q) == u, 1, 0)
                for r in residues
            ])
            solver.add(load >= 0, load <= 2)
            loads.append(load)
        solver.add(z3.PbEq([(load == 0, 1) for load in loads], 1))
        solver.add(z3.PbEq([(load == 2, 1) for load in loads], 1))

        # No dart may land in either deleted fibre or return to its source.
        for r in residues:
            for s in residues:
                u = (-t - r - s) % q
                y = (x + t + r) % q
                if u not in differences or (y, u) == (x, t):
                    solver.add(psi[x, t, r] != s)

    assumptions = []
    labels: dict[tuple[int, int], z3.BoolRef] = {}
    if not args.directed:
        for i, t in enumerate(differences):
            for u in differences[i:]:
                label = z3.Bool(f"recip_{t}_{u}")
                labels[t, u] = label
                assumptions.append(label)

        # If psi_(x,t)(r)=s, its target is
        # (x+t+r,-t-r-s), and the reverse local value is r.
        for x, t in cells:
            for r in residues:
                for s in residues:
                    u = (-t - r - s) % q
                    if u not in differences:
                        continue
                    y = (x + t + r) % q
                    if (y, u) == (x, t):
                        continue
                    key = (min(t, u), max(t, u))
                    solver.add(z3.Implies(
                        z3.And(labels[key], psi[x, t, r] == s),
                        psi[y, u, s] == r))

    solver.set(timeout=args.timeout_ms)
    result = solver.check(*assumptions)
    print(f"q={q} a={args.a % q} cells={len(cells)} "
          f"psi_variables={len(psi)}: {result}")

    if result == z3.unsat and args.reciprocity_core:
        core = list(solver.unsat_core())
        solver.set(timeout=5_000)
        for label in list(core):
            candidate = [other for other in core if not z3.eq(other, label)]
            if solver.check(*candidate) == z3.unsat:
                core = candidate
        print("  reciprocity_core=" +
              str(sorted(str(item) for item in core)))

    if result == z3.sat:
        model = solver.model()
        for t in differences:
            first = tuple(model.eval(psi[0, t, r]).as_long()
                          for r in residues)
            print(f"  psi_(0,{t})={dict(zip(residues, first))}")


if __name__ == "__main__":
    main()
