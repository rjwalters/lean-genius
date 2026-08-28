#!/usr/bin/env python3
"""Test whether the localized two-color obstruction needs O--O symmetry.

For a frozen three-open-code owner model, replace the ordinary graph by a
directed row-incidence matrix.  Edges incident to any code vertex retain their
forced symmetric owner semantics, but arcs between the 25 support-zero
vertices are independent in the two directions.  Exact row degrees and only
the support-zero/support-one common-neighbor caps for two selected colors are
retained.

UNSAT would nominate a bipartite Hall inequality.  SAT shows that the missing
ingredient is precisely symmetric f-factor / blossom coupling.
"""

from __future__ import annotations

import argparse

import z3

from probe_order49_three_open_code_holonomy import (
    CODES, PAIR01, PAIR02, PAIR12, build_solver, degree, support,
)


def directed_completion(
    owner_values: list[list[int]], selected_codes: set[int]
) -> tuple[z3.Solver, list[list[z3.BoolRef]]]:
    solver = z3.Solver()
    arc = [
        [z3.Bool(f"arc_{v}_{w}") for w in range(46)]
        for v in range(46)
    ]
    for v in range(46):
        solver.add(z3.Not(arc[v][v]))

    # Adjacency to every code vertex is completely fixed by ownership and
    # stays symmetric.  Only support-zero/support-zero arcs are relaxed.
    for h, code in enumerate(CODES):
        for v in range(46):
            for a in code:
                present = owner_values[h][v] == a
                solver.add(arc[v][a] == present)
                solver.add(arc[a][v] == present)

    for v in range(46):
        solver.add(z3.PbEq([(arc[v][w], 1) for w in range(46) if w != v], degree(v)))

    support_one_vertices = {
        u for h in selected_codes for u in CODES[h] if support(u) == 1
    }
    support_zero_vertices = [z for z in range(46) if support(z) == 0]
    for z in support_zero_vertices:
        for u in support_one_vertices:
            common = [z3.And(arc[z][w], arc[u][w]) for w in range(46)]
            solver.add(z3.PbLe([(term, 1) for term in common], 1))
    return solver, arc


def symmetric_lp_completion(
    owner_values: list[list[int]], selected_codes: set[int]
) -> z3.Solver:
    """Continuous relaxation of the symmetric support-zero edge problem."""
    solver = z3.Solver()
    zero_vertices = [v for v in range(46) if support(v) == 0]
    variables = {
        (v, w): z3.Real(f"x_{v}_{w}")
        for index, v in enumerate(zero_vertices)
        for w in zero_vertices[index + 1:]
    }
    for variable in variables.values():
        solver.add(variable >= 0, variable <= 1)

    def fixed_edge(v: int, w: int) -> bool:
        if v == w:
            return False
        endpoint = v if support(v) else w
        other = w if endpoint == v else v
        if not support(endpoint):
            raise ValueError("support-zero/support-zero edge is not fixed")
        h = next(index for index, code in enumerate(CODES) if endpoint in code)
        return owner_values[h][other] == endpoint

    def edge_value(v: int, w: int) -> z3.ArithRef:
        if v == w:
            return z3.RealVal(0)
        if support(v) or support(w):
            return z3.RealVal(int(fixed_edge(v, w)))
        return variables[min(v, w), max(v, w)]

    for v in range(46):
        solver.add(z3.Sum(*(edge_value(v, w) for w in range(46) if w != v)) == degree(v))

    support_one_vertices = {
        u for h in selected_codes for u in CODES[h] if support(u) == 1
    }
    for z in zero_vertices:
        for u in support_one_vertices:
            fixed_neighbors = [w for w in range(46) if fixed_edge(u, w)]
            solver.add(z3.Sum(*(edge_value(z, w) for w in fixed_neighbors)) <= 1)
    return solver


def scipy_symmetric_lp_completion(
    owner_values: list[list[int]], selected_codes: set[int], *,
    upper_bound: bool = True, extract_dual: bool = False,
) -> tuple[str, int, dict | None]:
    """Solve the same relaxation with HiGHS; return status and #fractionals."""
    import numpy as np
    from scipy.optimize import linprog

    zero_vertices = [v for v in range(46) if support(v) == 0]
    pairs = [
        (v, w) for index, v in enumerate(zero_vertices)
        for w in zero_vertices[index + 1:]
    ]
    pair_index = {pair: index for index, pair in enumerate(pairs)}

    def fixed_edge(v: int, w: int) -> bool:
        if v == w:
            return False
        endpoint = v if support(v) else w
        other = w if endpoint == v else v
        h = next(index for index, code in enumerate(CODES) if endpoint in code)
        return owner_values[h][other] == endpoint

    equalities = []
    equality_rhs = []
    for v in zero_vertices:
        row = np.zeros(len(pairs))
        for w in zero_vertices:
            if w != v:
                row[pair_index[min(v, w), max(v, w)]] = 1
        fixed_degree = sum(
            fixed_edge(v, w) for w in range(46) if support(w) > 0
        )
        equalities.append(row)
        equality_rhs.append(degree(v) - fixed_degree)

    inequalities = []
    inequality_rhs = []
    inequality_labels = []
    support_one_vertices = {
        u for h in selected_codes for u in CODES[h] if support(u) == 1
    }
    for z in zero_vertices:
        for u in support_one_vertices:
            row = np.zeros(len(pairs))
            fixed_common = 0
            for w in range(46):
                if not fixed_edge(u, w):
                    continue
                if support(w) == 0 and w != z:
                    row[pair_index[min(z, w), max(z, w)]] += 1
                elif support(w) > 0 and fixed_edge(z, w):
                    fixed_common += 1
            inequalities.append(row)
            inequality_rhs.append(1 - fixed_common)
            inequality_labels.append((z, u))
    result = linprog(
        np.zeros(len(pairs)),
        A_ub=np.array(inequalities), b_ub=np.array(inequality_rhs),
        A_eq=np.array(equalities), b_eq=np.array(equality_rhs),
        bounds=(0, 1 if upper_bound else None), method="highs",
    )
    if not result.success:
        status = "infeasible" if result.status == 2 else f"status{result.status}"
        certificate = None
        if result.status == 2 and extract_dual and not upper_bound:
            # Farkas ray for Aeq x=b, Aub x<=d, x>=0:
            # find y free and lambda>=0 with
            # y*Aeq + lambda*Aub >= 0, y*b+lambda*d = -1.
            from fractions import Fraction

            aeq = np.array(equalities)
            beq = np.array(equality_rhs)
            aub = np.array(inequalities)
            bub = np.array(inequality_rhs)
            columns = np.concatenate((aeq.T, -aeq.T, aub.T), axis=1)
            rhs_row = np.concatenate((beq, -beq, bub))[None, :]
            ray = linprog(
                np.ones(columns.shape[1]),
                A_ub=-columns, b_ub=np.zeros(columns.shape[0]),
                A_eq=rhs_row, b_eq=np.array([-1.0]),
                bounds=(0, None), method="highs",
            )
            if ray.success:
                count_eq = len(equalities)
                y = ray.x[:count_eq] - ray.x[count_eq:2 * count_eq]
                lam = ray.x[2 * count_eq:]
                certificate = {
                    "degree": [
                        (zero_vertices[index], str(Fraction(float(value)).limit_denominator(1000)))
                        for index, value in enumerate(y) if abs(value) > 1e-8
                    ],
                    "caps": [
                        (inequality_labels[index], str(Fraction(float(value)).limit_denominator(1000)))
                        for index, value in enumerate(lam) if value > 1e-8
                    ],
                    "nonnegative_edge_coefficients": int(np.sum(columns @ ray.x > 1e-8)),
                }
        return status, 0, certificate
    fractional = sum(1e-8 < value < 1 - 1e-8 for value in result.x)
    return "feasible", fractional, None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=16)
    parser.add_argument("--timeout-ms", type=int, default=10_000)
    parser.add_argument("--codes", default="0,1")
    parser.add_argument("--lp", action="store_true")
    parser.add_argument("--lp-no-upper", action="store_true")
    parser.add_argument("--lp-dual", action="store_true")
    args = parser.parse_args()
    if args.samples < 0:
        parser.error("--samples must be nonnegative")
    selected_codes = {int(value) for value in args.codes.split(",")}
    if len(selected_codes) != 2 or not selected_codes <= {0, 1, 2}:
        parser.error("--codes must select two distinct indices from {0,1,2}")

    owners, owner_variables = build_solver()
    owners.set(timeout=args.timeout_ms)
    outcomes: dict[str, int] = {}
    for sample in range(args.samples):
        owner_result = owners.check()
        if owner_result != z3.sat:
            outcomes[f"owner_{owner_result}"] = outcomes.get(f"owner_{owner_result}", 0) + 1
            break
        model = owners.model()
        values = [
            [model.eval(owner_variables[h][v]).as_long() for v in range(46)]
            for h in range(3)
        ]
        matching_profile = (
            int(values[0][PAIR01] == PAIR02),
            int(values[1][PAIR01] == PAIR12),
            int(values[2][PAIR02] == PAIR12),
        )
        fractional = None
        if args.lp:
            result, fractional, certificate = scipy_symmetric_lp_completion(
                values, selected_codes, upper_bound=not args.lp_no_upper,
                extract_dual=args.lp_dual,
            )
        else:
            completion = directed_completion(values, selected_codes)[0]
            completion.set(timeout=args.timeout_ms)
            result = str(completion.check())
        outcomes[str(result)] = outcomes.get(str(result), 0) + 1
        suffix = f" fractional={fractional}" if fractional is not None else ""
        print(
            f"{'lp' if args.lp else 'directed'}_completion_{sample} "
            f"profile={matching_profile} {result}{suffix}"
        )
        if args.lp and certificate is not None:
            print(f"lp_dual_{sample} {certificate}")
        owners.add(z3.Or(*(
            owner_variables[h][v] != values[h][v]
            for h in range(3) for v in range(46)
        )))
    print(f"{'lp' if args.lp else 'directed'}_completion_outcomes {outcomes}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
