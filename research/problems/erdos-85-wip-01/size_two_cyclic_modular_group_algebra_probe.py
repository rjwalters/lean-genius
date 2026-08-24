#!/usr/bin/env python3
"""Calibrate the F2[Z/2^k] augmentation filtration on cyclic routing models.

For a subset R of relative base displacements, encode its row polynomial as

    f_R(z) = sum_{r in R} z^r  in F2[z]/(z^q-1).

When q is a power of two this ring is F2[eps]/(eps^q), eps=z+1.  The script
extracts exact SAT models from ``size_two_cyclic_exact_graph_probe`` and
reports eps-adic valuations of every target-difference part of every routing
row.  In particular, a two-route collision at separation d has valuation
2^v2(d); this tests whether reciprocity changes, raises, or merely preserves
the proposed 2-adic collision level.

The default q=4 run uses the full same-difference cap.  At q=8 one can pass
``--c4-difference`` twice to inspect the known satisfiable two-fiber
relaxations; adding 0,2,4 is UNSAT for a=1.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from itertools import combinations, product
from math import comb

import z3

from size_two_cyclic_exact_graph_probe import build
from size_two_cyclic_packing_probe import (
    build_cnf as build_packing_cnf,
    solve_with_kissat,
)


def allowed_differences(q: int, a: int) -> list[int]:
    return [t for t in range(q) if t not in {a % q, (-1 - a) % q}]


def admissible_rows(q: int, t: int) -> list[int]:
    return [r for r in range(q) if t != r and t != (r - 1) % q]


def build_reduced_code(
    q: int, a: int, capped_differences: set[int] | None
) -> tuple[
    z3.Solver,
    list[int],
    dict[int, list[int]],
    dict[tuple[int, int, int], z3.IntNumRef],
]:
    """Build the exact reduced reciprocal code, deliberately allowing loops."""
    differences = allowed_differences(q, a)
    columns = [column for column in range(q) if column not in {0, q - 1}]
    rows = {t: admissible_rows(q, t) for t in differences}
    solver = z3.Solver()
    permutation: dict[tuple[int, int, int], z3.IntNumRef] = {}

    for x, t in product(range(q), differences):
        entries = []
        for row in rows[t]:
            value = z3.Int(f"p_{x}_{t}_{row}")
            permutation[x, t, row] = value
            solver.add(z3.Or([value == column for column in columns]))
            entries.append(value)
        solver.add(z3.Distinct(entries))

    capped = set(differences) if capped_differences is None else capped_differences
    for x, displacement, t in product(range(q), range(1, q), differences):
        if t not in capped:
            continue
        agreements = []
        for row in rows[t]:
            shifted = (row - displacement) % q
            if shifted in rows[t]:
                agreements.append(z3.If(
                    permutation[x, t, row] ==
                    (displacement + permutation[
                        (x + displacement) % q, t, shifted
                    ]) % q,
                    1,
                    0,
                ))
        solver.add(z3.Sum(agreements) <= 1)

    for x, t in product(range(q), differences):
        for row in rows[t]:
            column = permutation[x, t, row]
            reverse_cases = []
            for target_t in differences:
                reverse_row = (-row) % q
                if reverse_row not in rows[target_t]:
                    continue
                reverse_cases.append(z3.And(
                    column == (row + target_t) % q,
                    permutation[
                        (x + row) % q, target_t, reverse_row
                    ] == (t - row) % q,
                ))
            solver.add(z3.Or(reverse_cases))

    return solver, differences, rows, permutation


def augmentation_valuation(exponents: list[int], q: int) -> int:
    """Return the (z+1)-adic valuation, with q for the zero polynomial."""
    for degree in range(q):
        coefficient = sum(comb(r, degree) for r in exponents) % 2
        if coefficient:
            return degree
    return q


def v2(n: int) -> int:
    assert n > 0
    value = 0
    while n % 2 == 0:
        value += 1
        n //= 2
    return value


def half_quotient_signature(
    routes: list[tuple[int, int]], source_t: int, q: int
) -> tuple[str, tuple[tuple[str, int], ...]]:
    """Return the canonical boundary pairing and reverse-voltage signature.

    A route is ``(relative target row, relative target column)``.  Folding
    modulo ``q/2`` and cancelling cells with even multiplicity gives a
    bipartite graph of maximum degree two with four prescribed odd vertices.
    The two path components pair those vertices.  Each surviving edge is
    labelled by the high-bit xor of its reversed relative coordinates
    ``(-r, source_t-r)``.
    """
    m = q // 2
    cells: dict[tuple[int, int], list[tuple[int, int]]] = {}
    for row, column in routes:
        cells.setdefault((row % m, column % m), []).append((row, column))
    surviving = {cell: lifts for cell, lifts in cells.items() if len(lifts) % 2}
    assert all(len(lifts) == 1 for lifts in surviving.values())

    adjacency: dict[tuple[str, int], list[tuple[tuple[str, int], tuple[int, int]]]] = {}
    for cell in surviving:
        row_node = ("R", cell[0])
        col_node = ("C", cell[1])
        adjacency.setdefault(row_node, []).append((col_node, cell))
        adjacency.setdefault(col_node, []).append((row_node, cell))
    assert all(len(edges) <= 2 for edges in adjacency.values())

    boundary_names = {
        ("R", source_t % m): "R0",
        ("R", (source_t + 1) % m): "R1",
        ("C", 0): "C0",
        ("C", (-1) % m): "C1",
    }
    odd = {node for node, edges in adjacency.items() if len(edges) % 2}
    assert odd == set(boundary_names), (source_t, odd, set(boundary_names))

    def reverse_voltage(cell: tuple[int, int]) -> int:
        row, _column = surviving[cell][0]
        return (((-row) % q) // m) ^ (((source_t - row) % q) // m)

    visited_edges: set[tuple[int, int]] = set()
    paths: list[tuple[str, int]] = []
    for start in sorted(odd):
        incident = [cell for _neighbor, cell in adjacency[start]
                    if cell not in visited_edges]
        if not incident:
            continue
        node = start
        voltage = 0
        while True:
            choices = [(neighbor, cell) for neighbor, cell in adjacency[node]
                       if cell not in visited_edges]
            if not choices:
                break
            assert len(choices) == 1
            neighbor, cell = choices[0]
            visited_edges.add(cell)
            voltage ^= reverse_voltage(cell)
            node = neighbor
        assert node in odd and node != start
        endpoint_pair = "-".join(sorted((boundary_names[start], boundary_names[node])))
        paths.append((endpoint_pair, voltage))

    # Every remaining component is a cycle and has zero reverse voltage.
    for first_cell in surviving:
        if first_cell in visited_edges:
            continue
        node = ("R", first_cell[0])
        cycle_voltage = 0
        while True:
            choices = [(neighbor, cell) for neighbor, cell in adjacency[node]
                       if cell not in visited_edges]
            if not choices:
                break
            neighbor, cell = choices[0]
            visited_edges.add(cell)
            cycle_voltage ^= reverse_voltage(cell)
            node = neighbor
        assert cycle_voltage == 0
    assert len(visited_edges) == len(surviving)
    assert len(paths) == 2

    pairs = sorted(pair for pair, _voltage in paths)
    if all(pair[0] == pair[3] for pair in pairs):
        pairing = "RR|CC"
    else:
        pairing = "|".join(pairs)
    return pairing, tuple(sorted(paths))


def folded_pairing_signature(
    routes: list[tuple[int, int]], source_t: int, q: int
) -> tuple[str, tuple[tuple[str, int], ...]]:
    """Classify the mod-q/2 boundary pairing and reverse path voltages.

    ``routes`` contains relative (row, column) coordinates of one punctured
    permutation.  Fold the two lifts of every coordinate modulo m=q/2 and
    retain cells of odd multiplicity.  The resulting bipartite graph has
    maximum degree two and four degree-one boundary vertices.
    """
    m = q // 2
    surviving: dict[tuple[int, int], tuple[int, int]] = {}
    for row, column in routes:
        key = (row % m, column % m)
        if key in surviving:
            del surviving[key]
        else:
            surviving[key] = (row, column)

    adjacency: dict[tuple[str, int], list[tuple[tuple[str, int], int]]] = defaultdict(list)
    for (low_row, low_column), (row, _column) in surviving.items():
        row_node = ("R", low_row)
        column_node = ("C", low_column)
        reverse_row = (-row) % q
        reverse_column = (source_t - row) % q
        reverse_voltage = (reverse_row // m) ^ (reverse_column // m)
        adjacency[row_node].append((column_node, reverse_voltage))
        adjacency[column_node].append((row_node, reverse_voltage))

    assert all(len(neighbors) <= 2 for neighbors in adjacency.values())
    boundary_labels = {
        ("R", source_t % m): "R0",
        ("R", (source_t + 1) % m): "R1",
        ("C", 0): "C0",
        ("C", m - 1): "C1",
    }
    degree_one = {node for node, neighbors in adjacency.items() if len(neighbors) == 1}
    assert degree_one == set(boundary_labels), (source_t, degree_one, boundary_labels)

    seen: set[tuple[str, int]] = set()
    endpoint_paths: list[tuple[frozenset[str], int]] = []
    for start in adjacency:
        if start in seen:
            continue
        stack = [start]
        component: set[tuple[str, int]] = set()
        voltage = 0
        while stack:
            node = stack.pop()
            if node in component:
                continue
            component.add(node)
            seen.add(node)
            for neighbor, edge_voltage in adjacency[node]:
                # Count each undirected edge once.
                if node < neighbor:
                    voltage ^= edge_voltage
                if neighbor not in component:
                    stack.append(neighbor)
        endpoints = [node for node in component if len(adjacency[node]) == 1]
        if not endpoints:
            assert voltage == 0, (source_t, component, voltage)
            continue
        assert len(endpoints) == 2
        endpoint_paths.append((
            frozenset(boundary_labels[node] for node in endpoints), voltage
        ))

    pairs = {pair for pair, _ in endpoint_paths}
    rrcc = {frozenset({"R0", "R1"}), frozenset({"C0", "C1"})}
    direct = {frozenset({"R0", "C0"}), frozenset({"R1", "C1"})}
    swapped = {frozenset({"R0", "C1"}), frozenset({"R1", "C0"})}
    if pairs == rrcc:
        pairing = "RR|CC"
    elif pairs == direct:
        pairing = "R0C0|R1C1"
    elif pairs == swapped:
        pairing = "R0C1|R1C0"
    else:
        raise AssertionError((source_t, pairs))
    path_signature = tuple(sorted(
        ("".join(sorted(pair)), voltage) for pair, voltage in endpoint_paths
    ))
    return pairing, path_signature


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--c4-difference", type=int, action="append")
    parser.add_argument(
        "--encoding", choices=["graph", "reduced", "cnf"], default="graph",
        help=("graph is loopless; reduced/cnf are the exact code and permit "
              "loops; cnf uses kissat"),
    )
    args = parser.parse_args()

    q = args.q
    assert q >= 2 and q & (q - 1) == 0, "q must be a power of two"
    selected = None if args.c4_difference is None else {
        t % q for t in args.c4_difference
    }
    cnf_positive: set[int] | None = None
    cnf_ids: dict[tuple[int, int, int, int], int] | None = None
    if args.encoding == "graph":
        solver, vertices, edge = build(
            q,
            args.a,
            c4_pair_mode="same-difference",
            c4_differences=selected,
        )
        reduced_data = None
    elif args.encoding == "reduced":
        solver, differences, rows, permutation = build_reduced_code(
            q, args.a, selected
        )
        vertices = [(x, (x + t) % q) for x in range(q) for t in differences]
        edge = {}
        reduced_data = (differences, rows, permutation)
    else:
        packing_cnf = build_packing_cnf(
            q,
            args.a,
            cross_mode="same-t",
            agreement_ts=selected,
            reciprocity=True,
            loopless=False,
        )
        result, cnf_positive = solve_with_kissat(packing_cnf)
        cnf_ids = packing_cnf.ids
        differences = allowed_differences(q, args.a)
        rows = {t: admissible_rows(q, t) for t in differences}
        vertices = [(x, (x + t) % q) for x in range(q) for t in differences]
        edge = {}
        reduced_data = None
    if args.encoding != "cnf":
        solver.set(timeout=args.timeout_ms)
        result = solver.check()
    print(
        f"q={q} a={args.a % q} encoding={args.encoding} "
        f"selected={selected}: {result}"
    )
    if str(result) != "sat":
        return

    model = None if args.encoding == "cnf" else solver.model()
    index = {vertex: i for i, vertex in enumerate(vertices)}
    allowed = sorted({(y - x) % q for x, y in vertices})

    source_routes: dict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    if args.encoding == "cnf":
        assert cnf_positive is not None and cnf_ids is not None
        selected_keys = {
            key for key, variable in cnf_ids.items() if variable in cnf_positive
        }
        for x, source_t in product(range(q), differences):
            for row in rows[source_t]:
                column = next(
                    column for column in range(q)
                    if (x, source_t, row, column) in selected_keys
                )
                source_routes[x, source_t].append((row, column))
    elif reduced_data is None:
        def adjacent(u: tuple[int, int], v: tuple[int, int]) -> bool:
            i, j = index[u], index[v]
            if i == j:
                return False
            return z3.is_true(model.eval(edge[min(i, j), max(i, j)]))

        for x, y in vertices:
            source_t = (y - x) % q
            for target_x in range(q):
                for target_t in allowed:
                    target = (target_x, (target_x + target_t) % q)
                    if adjacent((x, y), target):
                        source_routes[x, source_t].append((
                            (target_x - x) % q,
                            (target[1] - x) % q,
                        ))
    else:
        differences, rows, permutation = reduced_data
        for x, source_t in product(range(q), differences):
            for row in rows[source_t]:
                column = model.eval(permutation[x, source_t, row]).as_long()
                source_routes[x, source_t].append((row, column))
    part_valuations: Counter[tuple[int, int]] = Counter()
    collision_pair_levels: Counter[tuple[int, int]] = Counter()
    half_quotient_signatures: Counter[
        tuple[int, str, tuple[tuple[str, int], ...]]
    ] = Counter()
    collision_count = 0

    for (x, source_t), routes in sorted(source_routes.items()):
        aggregate: list[int] = []
        for target_s in allowed:
            displacements = [
                row for row, column in routes
                if (column - row) % q == target_s
            ]
            if not displacements:
                continue
            aggregate.extend(displacements)
            valuation = augmentation_valuation(displacements, q)
            part_valuations[(len(displacements), valuation)] += 1
            for r, s in combinations(displacements, 2):
                collision_count += 1
                separation = (s - r) % q
                level = augmentation_valuation([r, s], q)
                predicted = 1 << v2(separation)
                assert level == predicted, (r, s, level, predicted)
                collision_pair_levels[(v2(separation), level)] += 1

        expected = [r for r in range(q) if r not in {source_t, (source_t + 1) % q}]
        assert sorted(aggregate) == expected
        assert augmentation_valuation(aggregate, q) == 1
        if q >= 4:
            pairing, path_voltages = half_quotient_signature(routes, source_t, q)
            half_quotient_signatures[(source_t, pairing, path_voltages)] += 1

    print(f"vertices={len(vertices)} allowed_differences={allowed}")
    print("target-part (cardinality, eps-valuation) distribution:")
    for key, count in sorted(part_valuations.items()):
        print(f"  {key}: {count}")
    print(f"collision_pairs={collision_count}")
    print("collision (v2(separation), eps-valuation) distribution:")
    for key, count in sorted(collision_pair_levels.items()):
        print(f"  {key}: {count}")
    if q >= 4:
        print("half-quotient (source_t, pairing, path reverse voltages) distribution:")
        for key, count in sorted(half_quotient_signatures.items()):
            print(f"  {key}: {count}")


if __name__ == "__main__":
    main()
