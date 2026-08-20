#!/usr/bin/env python3
"""Stochastic scout for the near-Latin lift model from ODD_EXISTENCE_GEOMETRY.

This is deliberately a discovery tool, not a certificate generator.  It fixes
the within-fiber perfect matchings by independent fiber relabeling and searches
over the remaining bipartite matchings.  The objective is

    sum_{u<v} choose(|N(u) intersect N(v)|, 2),

which is zero exactly when the resulting graph is C4-free.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import subprocess
import tempfile
from dataclasses import dataclass


@dataclass
class Datum:
    q: int
    # One permutation for an ordinary fiber pair, two for a paired pair.
    blocks: dict[tuple[int, int], list[list[int]]]
    # Involution on each fiber; None means the normalized (0 1)(2 3)... .
    within: list[list[int]] | None = None

    @property
    def m(self) -> int:
        return self.q - 1

    @property
    def r(self) -> int:
        return self.q + 1


def paired(i: int, j: int) -> bool:
    """The normalized fixed-point-free involution on fiber indices."""
    return (i ^ 1) == j


def random_datum(q: int, rng: random.Random) -> Datum:
    m, r = q - 1, q + 1
    blocks: dict[tuple[int, int], list[list[int]]] = {}
    for i in range(m):
        for j in range(i + 1, m):
            a = list(range(r))
            rng.shuffle(a)
            if paired(i, j):
                # b must be pointwise disjoint from a.  A cyclic shift of a
                # is a uniformly relabeled derangement and is cheap to seed.
                shift = rng.randrange(1, r)
                b = a[shift:] + a[:shift]
                blocks[i, j] = [a, b]
            else:
                blocks[i, j] = [a]
    return Datum(q, blocks)


def adjacency(datum: Datum) -> list[int]:
    m, r = datum.m, datum.r
    n = m * r
    adj = [0] * n

    def add(u: int, v: int) -> None:
        assert u != v and not ((adj[u] >> v) & 1)
        adj[u] |= 1 << v
        adj[v] |= 1 << u

    for i in range(m):
        mate = (datum.within[i] if datum.within is not None else
                [x ^ 1 for x in range(r)])
        for x in range(r):
            if x < mate[x]:
                add(i * r + x, i * r + mate[x])
    for (i, j), perms in datum.blocks.items():
        for perm in perms:
            for x, y in enumerate(perm):
                add(i * r + x, j * r + y)
    assert all(bits.bit_count() == datum.q for bits in adj)
    return adj


def objective(datum: Datum) -> int:
    adj = adjacency(datum)
    total = 0
    for u in range(len(adj)):
        for v in range(u + 1, len(adj)):
            common = (adj[u] & adj[v]).bit_count()
            total += common * (common - 1) // 2
    # Every C4 contributes its two opposite pairs.
    assert total % 2 == 0
    return total // 2


def propose_swap(datum: Datum, rng: random.Random):
    """Swap two images in one matching; return an undo record or None."""
    key = rng.choice(tuple(datum.blocks))
    perms = datum.blocks[key]
    which = rng.randrange(len(perms))
    perm = perms[which]
    x, y = rng.sample(range(datum.r), 2)
    if len(perms) == 2:
        other = perms[1 - which]
        if perm[y] == other[x] or perm[x] == other[y]:
            return None
    perm[x], perm[y] = perm[y], perm[x]
    return key, which, x, y


def undo(datum: Datum, record) -> None:
    key, which, x, y = record
    perm = datum.blocks[key][which]
    perm[x], perm[y] = perm[y], perm[x]


def search(q: int, restarts: int, steps: int, seed: int) -> tuple[int, Datum]:
    rng = random.Random(seed)
    global_best = math.inf
    best_datum: Datum | None = None
    for restart in range(restarts):
        datum = random_datum(q, rng)
        score = objective(datum)
        local_best = score
        # Reheat on each restart.  The scale is empirical: a random q=9 datum
        # has hundreds of C4s, while useful improvements are single swaps.
        for step in range(steps):
            record = propose_swap(datum, rng)
            if record is None:
                continue
            candidate = objective(datum)
            temperature = max(0.05, 3.0 * (1.0 - step / steps))
            accept = candidate <= score or rng.random() < math.exp(
                (score - candidate) / temperature
            )
            if accept:
                score = candidate
                local_best = min(local_best, score)
            else:
                undo(datum, record)
            if score < global_best:
                global_best = score
                best_datum = Datum(q, {
                    key: [perm.copy() for perm in perms]
                    for key, perms in datum.blocks.items()
                }, None if datum.within is None else
                    [mate.copy() for mate in datum.within])
                print(
                    f"restart={restart} step={step} best_C4={global_best}",
                    flush=True,
                )
            if score == 0:
                assert best_datum is not None
                return 0, best_datum
        print(
            f"restart={restart} final_C4={score} local_best={local_best}",
            flush=True,
        )
    assert best_datum is not None
    return int(global_best), best_datum


def serializable(datum: Datum) -> dict[str, object]:
    return {
        "q": datum.q,
        "fiber_pairing": [[i, i ^ 1] for i in range(0, datum.m, 2)],
        "within_fiber_matchings": [
            [[x, mate[x]] for x in range(datum.r) if x < mate[x]]
            for mate in (datum.within if datum.within is not None else
                [[x ^ 1 for x in range(datum.r)] for _ in range(datum.m)])
        ],
        "blocks": {
            f"{i},{j}": perms for (i, j), perms in sorted(datum.blocks.items())
        },
    }


def decompose_two_regular(rows: list[list[int]]) -> list[list[int]]:
    """Split a 2-regular bipartite graph into two perfect matchings."""
    r = len(rows)
    match_y = [-1] * r

    def augment(x: int, seen: set[int]) -> bool:
        for y in rows[x]:
            if y in seen:
                continue
            seen.add(y)
            if match_y[y] < 0 or augment(match_y[y], seen):
                match_y[y] = x
                return True
        return False

    for x in range(r):
        assert augment(x, set())
    first = [-1] * r
    for y, x in enumerate(match_y):
        first[x] = y
    second = [next(y for y in rows[x] if y != first[x]) for x in range(r)]
    assert sorted(first) == list(range(r))
    assert sorted(second) == list(range(r))
    return [first, second]


def sat_search(q: int, timeout: int, paired_cycles: list[str] | None = None
               ) -> tuple[str, Datum | None, dict[str, int]]:
    """Exact CNF model of the lift class, solved by Kissat."""
    m, r = q - 1, q + 1
    n = m * r
    variables: dict[tuple[int, int], int] = {}
    reverse: dict[int, tuple[int, int]] = {}
    next_var = 1
    if paired_cycles is not None:
        if len(paired_cycles) != m // 2:
            raise ValueError(f"expected {m // 2} paired cycle types")
        # Once doubled cross-fiber graphs are put in canonical form, the
        # within-fiber matchings must remain variable; fixing both is not a
        # legitimate use of the same relabeling freedom.
        for i in range(m):
            for x in range(r):
                for y in range(x + 1, r):
                    u, v = i * r + x, i * r + y
                    variables[u, v] = next_var
                    reverse[next_var] = (u, v)
                    next_var += 1
    for i in range(m):
        for j in range(i + 1, m):
            for x in range(r):
                for y in range(r):
                    u, v = i * r + x, j * r + y
                    variables[u, v] = next_var
                    reverse[next_var] = (u, v)
                    next_var += 1

    def edge(u: int, v: int) -> bool | int:
        if u == v:
            return False
        if u > v:
            u, v = v, u
        i, x = divmod(u, r)
        j, y = divmod(v, r)
        if i == j:
            return variables[u, v] if paired_cycles is not None else x // 2 == y // 2
        return variables[u, v]

    stats = {"degree_clauses": 0, "gauge_clauses": 0, "c4_clauses": 0}
    with tempfile.NamedTemporaryFile(mode="w+", suffix=".cnf") as cnf:
        # Fixed-width header, overwritten after streaming the body.
        cnf.write(f"p cnf {next_var - 1:12d} {0:15d}\n")
        clause_count = 0

        def emit(lits) -> None:
            nonlocal clause_count
            reduced = []
            for lit in lits:
                if lit is True:
                    return
                if lit is False:
                    continue
                reduced.append(int(lit))
            reduced = sorted(set(reduced), key=abs)
            if not reduced:
                raise ValueError("fixed edges already contain a forbidden C4")
            cnf.write(" ".join(map(str, reduced)) + " 0\n")
            clause_count += 1

        def exactly(lits: list[int], degree: int) -> None:
            # At least degree: every set of n-degree+1 omitted candidates
            # leaves a clause of size n-degree+1.
            for subset in itertools.combinations(lits, len(lits) - degree + 1):
                emit(subset)
                stats["degree_clauses"] += 1
            # At most degree.
            for subset in itertools.combinations(lits, degree + 1):
                emit([-x for x in subset])
                stats["degree_clauses"] += 1

        for i in range(m):
            if paired_cycles is not None:
                for x in range(r):
                    exactly([
                        int(edge(i * r + x, i * r + y))
                        for y in range(r) if y != x
                    ], 1)
            for j in range(i + 1, m):
                degree = 2 if paired(i, j) else 1
                for x in range(r):
                    exactly([int(edge(i * r + x, j * r + y)) for y in range(r)], degree)
                for y in range(r):
                    exactly([int(edge(i * r + x, j * r + y)) for x in range(r)], degree)

        if paired_cycles is not None:
            # Normalize each doubled pair independently.  Its union of two
            # matchings is an even-cycle decomposition; after fixing one
            # matching to the identity, half-cycle lengths give the cycles
            # of the relative permutation.
            for pair_index, i in enumerate(range(0, m, 2)):
                j = i ^ 1
                parts = [int(x) // 2 for x in paired_cycles[pair_index].split("+")]
                if sum(parts) != r or any(length < 3 for length in parts):
                    raise ValueError(
                        "paired cycle lengths must be even, at least 6, "
                        "and sum to 2(q+1)"
                    )
                successor = list(range(r))
                start = 0
                for length in parts:
                    for x in range(start, start + length):
                        successor[x] = start + (x - start + 1) % length
                    start += length
                for x in range(r):
                    for y in range(r):
                        variable = int(edge(i * r + x, j * r + y))
                        emit([variable if y in (x, successor[x]) else -variable])
                        stats["gauge_clauses"] += 1

        # Three possible undirected 4-cycles on every four-point set.
        def negated_edge(e: bool | int) -> bool | int:
            # bool is a subclass of int in Python, so test it first.
            return (not e) if isinstance(e, bool) else -e

        for a, b, c, d in itertools.combinations(range(n), 4):
            for cycle in (
                ((a, b), (b, c), (c, d), (d, a)),
                ((a, b), (b, d), (d, c), (c, a)),
                ((a, c), (c, b), (b, d), (d, a)),
            ):
                before = clause_count
                emit([negated_edge(e)
                      for e in (edge(u, v) for u, v in cycle)])
                stats["c4_clauses"] += clause_count - before

        cnf.flush()
        cnf.seek(0)
        cnf.write(f"p cnf {next_var - 1:12d} {clause_count:15d}\n")
        cnf.flush()
        stats["variables"] = next_var - 1
        stats["clauses"] = clause_count
        try:
            result = subprocess.run(
                ["kissat", "--no-color", cnf.name],
                capture_output=True, text=True,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            return "UNKNOWN-TIMEOUT", None, stats

    output = result.stdout + "\n" + result.stderr
    if "s UNSATISFIABLE" in output:
        return "UNSAT", None, stats
    if "s SATISFIABLE" not in output:
        diagnostic = " | ".join(output.strip().splitlines()[-3:])
        return f"UNKNOWN-RC-{result.returncode}: {diagnostic}", None, stats
    true_vars = set()
    for line in output.splitlines():
        if line.startswith("v "):
            true_vars.update(int(x) for x in line.split()[1:] if int(x) > 0)
    within = None
    if paired_cycles is not None:
        within = []
        for i in range(m):
            mate = [-1] * r
            for x in range(r):
                for y in range(x + 1, r):
                    if int(edge(i * r + x, i * r + y)) in true_vars:
                        mate[x] = y
                        mate[y] = x
            assert all(y >= 0 for y in mate)
            within.append(mate)
    rows_by_block: dict[tuple[int, int], list[list[int]]] = {}
    for i in range(m):
        for j in range(i + 1, m):
            rows = [[] for _ in range(r)]
            for x in range(r):
                for y in range(r):
                    if int(edge(i * r + x, j * r + y)) in true_vars:
                        rows[x].append(y)
            degree = 2 if paired(i, j) else 1
            assert all(len(row) == degree for row in rows)
            rows_by_block[i, j] = (
                decompose_two_regular(rows) if degree == 2
                else [[row[0] for row in rows]]
            )
    datum = Datum(q, rows_by_block, within)
    assert objective(datum) == 0
    return "SAT", datum, stats


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", type=int, default=9)
    parser.add_argument("--restarts", type=int, default=10)
    parser.add_argument("--steps", type=int, default=100_000)
    parser.add_argument("--seed", type=int, default=85)
    parser.add_argument("--method", choices=("sat", "stochastic"), default="sat")
    parser.add_argument("--timeout", type=int, default=3600,
                        help="Kissat timeout in seconds")
    cycle_types = ("20", "6+14", "8+12", "10+10")
    parser.add_argument(
        "--paired-cycle", choices=cycle_types,
        help="q=9 scout: fix every doubled fiber pair to this cycle type",
    )
    parser.add_argument(
        "--paired-cycles",
        help=("q=9 scout: comma-separated cycle type for each of the four "
              "doubled fiber pairs, e.g. '20,20,6+14,8+12'"),
    )
    parser.add_argument(
        "--enumerate-cycle-multisets", action="store_true",
        help="run all 35 symmetry-reduced q=9 mixed cycle-type multisets",
    )
    parser.add_argument(
        "--multiset-start", type=int, default=0,
        help="zero-based first multiset representative to run",
    )
    parser.add_argument(
        "--multiset-count", type=int,
        help="maximum number of multiset representatives to run",
    )
    parser.add_argument("--output")
    args = parser.parse_args()
    if args.q < 3 or args.q % 2 == 0:
        parser.error("q must be an odd integer at least 3")
    if args.paired_cycle and args.paired_cycles:
        parser.error("use at most one of --paired-cycle and --paired-cycles")
    if args.enumerate_cycle_multisets and (args.paired_cycle or args.paired_cycles):
        parser.error("cycle multiset enumeration cannot be combined with a fixed type")
    if args.enumerate_cycle_multisets:
        if args.q != 9 or args.method != "sat":
            parser.error("cycle multiset enumeration is an exact q=9 SAT scout")
        if args.multiset_start < 0:
            parser.error("--multiset-start must be nonnegative")
        if args.multiset_count is not None and args.multiset_count < 1:
            parser.error("--multiset-count must be positive")
        summaries = []
        representatives = list(itertools.combinations_with_replacement(
            cycle_types, 4
        ))
        stop = (None if args.multiset_count is None else
                args.multiset_start + args.multiset_count)
        for representative_index, cycles in enumerate(
            representatives[args.multiset_start:stop], args.multiset_start
        ):
            status, datum, stats = sat_search(args.q, args.timeout, list(cycles))
            item = {
                "representative_index": representative_index,
                "paired_cycles": cycles,
                "status": status,
                "stats": stats,
            }
            if datum is not None:
                item |= serializable(datum) | {"C4_count": 0}
            summaries.append(item)
            print(json.dumps(item, sort_keys=True), flush=True)
            if datum is not None:
                break
        result = {
            "q": args.q,
            "representative_count": len(representatives),
            "cycle_multiset_scouts": summaries,
        }
    elif args.method == "sat":
        paired_cycles = None
        if args.paired_cycle:
            paired_cycles = [args.paired_cycle] * ((args.q - 1) // 2)
        elif args.paired_cycles:
            paired_cycles = args.paired_cycles.split(",")
            if any(cycle not in cycle_types for cycle in paired_cycles):
                parser.error(f"cycle types must be chosen from {cycle_types}")
        status, datum, stats = sat_search(args.q, args.timeout, paired_cycles)
        result = {"q": args.q, "status": status, "stats": stats}
        if datum is not None:
            result |= serializable(datum) | {"C4_count": 0}
    else:
        score, datum = search(args.q, args.restarts, args.steps, args.seed)
        result = serializable(datum) | {
            "C4_count": score, "status": "SAT" if score == 0 else "HEURISTIC",
        }
    print(json.dumps(result, sort_keys=True))
    if args.output:
        with open(args.output, "w") as stream:
            json.dump(result, stream, sort_keys=True, indent=2)
            stream.write("\n")


if __name__ == "__main__":
    main()
