#!/usr/bin/env python3
"""SAT probe for the q=9 three-high second-profile 24-core.

This is an abstraction of the Lean-proved zero-slack pair decomposition.
The 24 unmarked B1 vertices have three high colors of size eight.  The model
simultaneously chooses

* the cubic original graph K, with one neighbor of each color at every point;
* 26 rainbow B0 triples, in the branch-specific parallel-class pattern;
* one seven-edge marked-support matching on each pair of colors;
* the 21 zero-common-neighbor (defect) pairs; and
* the six defect edges from the three marked B1 points.

Every cross-color pair is covered exactly once by a K-neighborhood block, a
B0 triple, a marked-support pair, or a defect edge.  Same-color pairs already
share their high root, so they may have no further common neighbor or defect
edge.

This script is an exploratory finite certificate, not a kernel-checked proof.
"""

from __future__ import annotations

import argparse
import json
import time
from itertools import combinations, product

from z3 import And, Bool, If, Or, Solver, Sum, sat, unknown


N_COLOR = 3
N_PER_COLOR = 8
N = N_COLOR * N_PER_COLOR


def color(v: int) -> int:
    return v // N_PER_COLOR


def edge_key(u: int, v: int) -> tuple[int, int]:
    assert u != v
    return (u, v) if u < v else (v, u)


def exactly_one(xs):
    return Sum([If(x, 1, 0) for x in xs]) == 1


def at_most_one(xs):
    return Sum([If(x, 1, 0) for x in xs]) <= 1


def build(branch: int, timeout_ms: int) -> tuple[Solver, dict]:
    if branch not in (3, 4):
        raise ValueError("branch must be 3 or 4")

    solver = Solver()
    solver.set(timeout=timeout_ms)

    pairs = list(combinations(range(N), 2))
    cross_pairs = [(u, v) for u, v in pairs if color(u) != color(v)]
    same_pairs = [(u, v) for u, v in pairs if color(u) == color(v)]

    # Original cubic core.
    k = {e: Bool(f"k_{e[0]}_{e[1]}") for e in pairs}

    def kadj(u: int, v: int):
        if u == v:
            return False
        return k[edge_key(u, v)]

    for u in range(N):
        for c in range(N_COLOR):
            solver.add(
                exactly_one(
                    [kadj(u, v) for v in range(N) if v != u and color(v) == c]
                )
            )

    # Rainbow triples, indexed by one point of each color.
    triples = list(product(range(8), range(8, 16), range(16, 24)))
    selected = {t: Bool(f"triple_{t[0]}_{t[1]}_{t[2]}") for t in triples}

    if branch == 3:
        classes = [
            {t: Bool(f"class_{r}_{t[0]}_{t[1]}_{t[2]}") for t in triples}
            for r in range(3)
        ]
        holes = {t: Bool(f"hole_{t[0]}_{t[1]}_{t[2]}") for t in triples}
        for t in triples:
            roles = [classes[r][t] for r in range(3)] + [holes[t]]
            solver.add(selected[t] == Or(roles))
            solver.add(at_most_one(roles))
        for r in range(3):
            solver.add(Sum([If(classes[r][t], 1, 0) for t in triples]) == 8)
            for v in range(N):
                solver.add(
                    exactly_one([classes[r][t] for t in triples if v in t])
                )
        solver.add(Sum([If(holes[t], 1, 0) for t in triples]) == 2)
    else:
        classes = [
            {t: Bool(f"class_{r}_{t[0]}_{t[1]}_{t[2]}") for t in triples}
            for r in range(3)
        ]
        holes = {t: Bool(f"hole_{t[0]}_{t[1]}_{t[2]}") for t in triples}
        for t in triples:
            roles = [classes[r][t] for r in range(3)] + [holes[t]]
            solver.add(selected[t] == Or(roles))
            solver.add(at_most_one(roles))
        solver.add(Sum([If(classes[0][t], 1, 0) for t in triples]) == 8)
        for v in range(N):
            solver.add(exactly_one([classes[0][t] for t in triples if v in t]))
        for r in (1, 2):
            solver.add(Sum([If(classes[r][t], 1, 0) for t in triples]) == 7)
            for v in range(N):
                solver.add(at_most_one([classes[r][t] for t in triples if v in t]))
        solver.add(Sum([If(holes[t], 1, 0) for t in triples]) == 4)

    solver.add(Sum([If(selected[t], 1, 0) for t in triples]) == 26)

    # The three marked supports give seven-pair matchings, one on each pair
    # of colors.  The matching on colors c,d belongs to the marked point of
    # the third color.
    marked_pairs = {}
    for c, d in combinations(range(N_COLOR), 2):
        es = [
            (u, v)
            for u in range(N)
            for v in range(N)
            if color(u) == c and color(v) == d
        ]
        for u, v in es:
            marked_pairs[edge_key(u, v)] = Bool(f"marked_pair_{u}_{v}")
        solver.add(
            Sum([If(marked_pairs[edge_key(u, v)], 1, 0) for u, v in es]) == 7
        )
        for u in range(N):
            if color(u) == c:
                solver.add(
                    at_most_one(
                        [marked_pairs[edge_key(u, v)] for _, v in es if _ == u]
                    )
                )
            elif color(u) == d:
                solver.add(
                    at_most_one(
                        [marked_pairs[edge_key(v, u)] for v, _ in es if _ == u]
                    )
                )

    # Defect graph on U1.
    defect = {edge_key(u, v): Bool(f"defect_{u}_{v}") for u, v in cross_pairs}

    def common_k_terms(u: int, v: int):
        return [And(kadj(u, w), kadj(v, w)) for w in range(N) if w not in (u, v)]

    # Same-color pairs already share their high root; no low common center.
    for u, v in same_pairs:
        solver.add(Sum([If(q, 1, 0) for q in common_k_terms(u, v)]) == 0)

    # Exact zero-slack cover of every cross-color pair.
    for u, v in cross_pairs:
        triple_terms = [selected[t] for t in triples if u in t and v in t]
        terms = common_k_terms(u, v) + triple_terms + [marked_pairs[edge_key(u, v)], defect[edge_key(u, v)]]
        solver.add(Sum([If(q, 1, 0) for q in terms]) == 1)

    solver.add(Sum([If(defect[e], 1, 0) for e in defect]) == 21)
    defect_degree = {}
    for u in range(N):
        incident = [defect[edge_key(u, v)] for v in range(N) if color(v) != color(u)]
        defect_degree[u] = Sum([If(q, 1, 0) for q in incident])
        solver.add(defect_degree[u] <= 2)

    # Restore the three marked B1 vertices.  Marked point c has two defect
    # neighbors outside its own high color.  Each unmarked point receives
    # exactly the deficit needed to reach degree two in the full B1 core.
    attach = {
        (c, v): Bool(f"attach_{c}_{v}")
        for c in range(N_COLOR)
        for v in range(N)
        if color(v) != c
    }
    for c in range(N_COLOR):
        solver.add(Sum([If(attach[c, v], 1, 0) for v in range(N) if color(v) != c]) == 2)
    for v in range(N):
        solver.add(
            Sum([If(attach[c, v], 1, 0) for c in range(N_COLOR) if c != color(v)])
            + defect_degree[v]
            == 2
        )

    # The already-proved full 27-point color ledger has nine defect edges
    # between every pair of high colors.
    for c, d in combinations(range(N_COLOR), 2):
        internal = Sum(
            [
                If(defect[edge_key(u, v)], 1, 0)
                for u in range(N)
                for v in range(N)
                if color(u) == c and color(v) == d
            ]
        )
        removed = Sum(
            [If(attach[c, v], 1, 0) for v in range(N) if color(v) == d]
            + [If(attach[d, v], 1, 0) for v in range(N) if color(v) == c]
        )
        solver.add(internal + removed == 9)

    return solver, {
        "k": k,
        "triples": triples,
        "selected": selected,
        "classes": classes,
        "holes": holes,
        "marked_pairs": marked_pairs,
        "defect": defect,
        "attach": attach,
    }


def selected_items(model, mapping):
    return [key for key, value in mapping.items() if bool(model.eval(value, model_completion=True))]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), required=True)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    solver, data = build(args.branch, args.timeout_seconds * 1000)
    started = time.time()
    result = solver.check()
    elapsed = time.time() - started
    summary = {
        "branch": args.branch,
        "result": str(result),
        "elapsed_seconds": round(elapsed, 3),
        "reason_unknown": solver.reason_unknown() if result == unknown else None,
    }

    if result == sat:
        model = solver.model()
        summary.update(
            {
                "k_edges": selected_items(model, data["k"]),
                "triples": selected_items(model, data["selected"]),
                "classes": [selected_items(model, c) for c in data["classes"]],
                "holes": selected_items(model, data["holes"]),
                "marked_pairs": selected_items(model, data["marked_pairs"]),
                "defect_edges": selected_items(model, data["defect"]),
                "marked_attachments": selected_items(model, data["attach"]),
            }
        )

    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        print(f"branch={args.branch} result={result} elapsed={elapsed:.3f}s")
        if result == unknown:
            print(f"reason_unknown={solver.reason_unknown()}")
        elif result == sat:
            print(f"k_edges={len(summary['k_edges'])}")
            print(f"triples={len(summary['triples'])}")
            print(f"marked_pairs={len(summary['marked_pairs'])}")
            print(f"defect_edges={len(summary['defect_edges'])}")
            print(f"marked_attachments={len(summary['marked_attachments'])}")
    return 0 if result != unknown else 2


if __name__ == "__main__":
    raise SystemExit(main())
