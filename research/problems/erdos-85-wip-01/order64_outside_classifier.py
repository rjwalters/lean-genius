#!/usr/bin/env python3
"""Finite feasibility probe for the order-64 H16 outside block.

For a prescribed cycle partition of H on 16 vertices, enumerate simple
6-regular graphs R such that R commutes with H and avoids H-distance-two
pairs.  Regard the 48 edges of R as the outside vertices, with incidence
matrix B.  For each R, test whether there is a symmetric simple graph C on
those 48 edges satisfying the exact cross-block equation

    H B + B C = J.

The R model also enforces the formally established all-or-none overlap on
each H-cycle.  The C model enforces C4-freeness on the outside block, a
necessary condition for an ambient solution.  This remains a diagnostic
classifier rather than a replayable proof certificate.
"""

from __future__ import annotations

import argparse
from itertools import combinations, permutations, product
from pathlib import Path

import numpy as np
import z3
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


PARTITIONS = {
    "16": [16],
    "10,6": [10, 6],
    "8,8": [8, 8],
    "5,5,3,3": [5, 5, 3, 3],
}


def cycle_adjacency(parts: list[int]) -> np.ndarray:
    h = np.zeros((16, 16), dtype=int)
    base = 0
    for length in parts:
        for i in range(length):
            u = base + i
            v = base + (i + 1) % length
            h[u, v] = h[v, u] = 1
        base += length
    assert base == 16
    return h


def cycle_automorphism_edge_maps(parts: list[int], pairs: list[tuple[int, int]]):
    """Precompute the action of every cycle-union automorphism on pairs."""
    offsets, base = [], 0
    for length in parts:
        offsets.append(base)
        base += length
    groups: dict[int, list[int]] = {}
    for i, length in enumerate(parts):
        groups.setdefault(length, []).append(i)
    partial_groups = []
    for length, components in groups.items():
        group_maps = []
        transforms = list(product(range(length), (1, -1)))
        for component_perm in permutations(range(len(components))):
            for choices in product(transforms, repeat=len(components)):
                mapping = {}
                for source_pos, source_component in enumerate(components):
                    target_component = components[component_perm[source_pos]]
                    rotation, sign = choices[source_pos]
                    for i in range(length):
                        mapping[offsets[source_component] + i] = \
                            offsets[target_component] + (rotation + sign * i) % length
                group_maps.append(mapping)
        partial_groups.append(group_maps)
    vertex_maps = []
    for pieces in product(*partial_groups):
        mapping = {}
        for piece in pieces:
            mapping.update(piece)
        vertex_maps.append(mapping)
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    edge_maps = np.empty((len(vertex_maps), len(pairs)), dtype=np.int16)
    for a, mapping in enumerate(vertex_maps):
        for i, (u, v) in enumerate(pairs):
            edge_maps[a, i] = pair_index[tuple(sorted((mapping[u], mapping[v])))]
    return edge_maps


def solve_binary(nvars: int, rows: list[dict[int, int]],
                 lower: list[int], upper: list[int], binary_prefix: int | None = None):
    data, rr, cc = [], [], []
    for i, row in enumerate(rows):
        for j, value in row.items():
            if value:
                rr.append(i)
                cc.append(j)
                data.append(value)
    matrix = coo_matrix((data, (rr, cc)), shape=(len(rows), nvars)).tocsr()
    if binary_prefix is None:
        binary_prefix = nvars
    integrality = np.zeros(nvars)
    integrality[:binary_prefix] = 1
    return milp(
        np.zeros(nvars), integrality=integrality,
        bounds=Bounds(np.zeros(nvars), np.ones(nvars)),
        constraints=LinearConstraint(matrix, np.array(lower), np.array(upper)),
        options={"presolve": True, "time_limit": 120},
    )


def r_base_model(h: np.ndarray):
    pairs = list(combinations(range(16), 2))
    index = {p: i for i, p in enumerate(pairs)}

    def var(u: int, v: int):
        if u == v:
            return None
        return index[tuple(sorted((u, v)))]

    rows: list[dict[int, int]] = []
    lo: list[int] = []
    hi: list[int] = []
    for u in range(16):
        row = {var(u, v): 1 for v in range(16) if v != u}
        rows.append(row)
        lo.append(6)
        hi.append(6)
    for u in range(16):
        for v in range(16):
            row: dict[int, int] = {}
            for k in range(16):
                if h[u, k] and k != v:
                    j = var(k, v)
                    row[j] = row.get(j, 0) + 1
                if h[k, v] and u != k:
                    j = var(u, k)
                    row[j] = row.get(j, 0) - 1
            if row:
                rows.append(row)
                lo.append(0)
                hi.append(0)
    h2 = h @ h
    for u, v in pairs:
        if h2[u, v] > 0:
            rows.append({var(u, v): 1})
            lo.append(0)
            hi.append(0)

    # Formal parity consequence (Erdos85EvenFactorOverlap): on each
    # connected H-cycle, either every H-edge belongs to R or none does.
    unseen = set(range(16))
    while unseen:
        root = next(iter(unseen))
        component = {root}
        frontier = [root]
        unseen.remove(root)
        while frontier:
            u = frontier.pop()
            for v in np.flatnonzero(h[u]):
                v = int(v)
                if v in unseen:
                    unseen.remove(v)
                    component.add(v)
                    frontier.append(v)
        hedges = [(u, v) for u, v in pairs
                  if u in component and v in component and h[u, v]]
        anchor = var(*hedges[0])
        for edge in hedges[1:]:
            rows.append({var(*edge): 1, anchor: -1})
            lo.append(0)
            hi.append(0)
    return pairs, rows, lo, hi


def make_r_solver(h: np.ndarray):
    """Build the exact commuting/separated R model in Z3."""
    pairs = list(combinations(range(16), 2))
    index = {p: i for i, p in enumerate(pairs)}
    rvars = [z3.Bool(f"r_{u}_{v}") for u, v in pairs]

    def var(u: int, v: int):
        if u == v:
            return z3.BoolVal(False)
        return rvars[index[tuple(sorted((u, v)))]]

    solver = z3.Solver()
    for u in range(16):
        solver.add(z3.PbEq([(var(u, v), 1)
                            for v in range(16) if v != u], 6))
    for u in range(16):
        for v in range(16):
            lhs = z3.Sum([z3.If(var(k, v), 1, 0)
                          for k in range(16) if h[u, k]])
            rhs = z3.Sum([z3.If(var(u, k), 1, 0)
                          for k in range(16) if h[k, v]])
            solver.add(lhs == rhs)
    h2 = h @ h
    for u, v in pairs:
        if h2[u, v] > 0:
            solver.add(z3.Not(var(u, v)))
    unseen = set(range(16))
    while unseen:
        root = next(iter(unseen))
        component = {root}
        frontier = [root]
        unseen.remove(root)
        while frontier:
            u = frontier.pop()
            for v in np.flatnonzero(h[u]):
                v = int(v)
                if v in unseen:
                    unseen.remove(v)
                    component.add(v)
                    frontier.append(v)
        hedges = [(u, v) for u, v in pairs
                  if u in component and v in component and h[u, v]]
        anchor = var(*hedges[0])
        for edge in hedges[1:]:
            solver.add(var(*edge) == anchor)
    return pairs, rvars, solver


def c_feasible(h: np.ndarray, redges: list[tuple[int, int]]):
    assert len(redges) == 48
    incidence = np.zeros((16, 48), dtype=int)
    for e, (u, v) in enumerate(redges):
        incidence[u, e] = incidence[v, e] = 1
    target = 1 - h @ incidence
    if target.min() < 0 or target.max() > 1:
        return "DEAD", None, 0, 0

    allowed = []
    for e, f in combinations(range(48), 2):
        if np.all(incidence[:, f] <= target[:, e]) and \
                np.all(incidence[:, e] <= target[:, f]):
            allowed.append((e, f))
    cindex = {p: i for i, p in enumerate(allowed)}
    cvars = [z3.Bool(f"c_{e}_{f}") for e, f in allowed]
    solver = z3.Solver()
    solver.set(timeout=120_000)
    for e in range(48):
        for u in range(16):
            terms = []
            for f in range(48):
                if e == f or not incidence[u, f]:
                    continue
                p = tuple(sorted((e, f)))
                if p in cindex:
                    terms.append(cvars[cindex[p]])
            if not terms:
                if target[u, e] != 0:
                    return "DEAD", None, len(allowed), 0
                continue
            solver.add(z3.PbEq([(term, 1) for term in terms],
                               int(target[u, e])))
    common_term_count = 0
    for a, b in combinations(range(48), 2):
        common = []
        for c in range(48):
            if c in (a, b):
                continue
            ac = tuple(sorted((a, c)))
            bc = tuple(sorted((b, c)))
            if ac not in cindex or bc not in cindex:
                continue
            common.append(z3.And(cvars[cindex[ac]], cvars[cindex[bc]]))
        common_term_count += len(common)
        if len(common) > 1:
            solver.add(z3.AtMost(*common, 1))
    result = solver.check()
    if result == z3.unsat:
        return "DEAD", None, len(allowed), common_term_count
    if result == z3.unknown:
        return "UNKNOWN", None, len(allowed), common_term_count
    model = solver.model()
    chosen = [allowed[i] for i, x in enumerate(cvars)
              if z3.is_true(model.eval(x))]
    return "ALIVE", chosen, len(allowed), common_term_count


def emit_c_cnf(h: np.ndarray, redges: list[tuple[int, int]], path: Path):
    """Write the outside-C necessary conditions as an elementary CNF."""
    incidence = np.zeros((16, 48), dtype=int)
    for e, (u, v) in enumerate(redges):
        incidence[u, e] = incidence[v, e] = 1
    target = 1 - h @ incidence
    if target.min() < 0 or target.max() > 1:
        path.write_text("p cnf 1 2\n1 0\n-1 0\n")
        return 1, 2
    allowed = []
    for e, f in combinations(range(48), 2):
        if np.all(incidence[:, f] <= target[:, e]) and \
                np.all(incidence[:, e] <= target[:, f]):
            allowed.append((e, f))
    cindex = {edge: i + 1 for i, edge in enumerate(allowed)}
    clauses: list[list[int]] = []
    # Each (outside edge e, inside vertex u) receives exactly target[u,e]
    # service neighbors through endpoints of C-neighbors.
    for e in range(48):
        for u in range(16):
            terms = []
            for f in range(48):
                p = tuple(sorted((e, f)))
                if e != f and incidence[u, f] and p in cindex:
                    terms.append(cindex[p])
            if target[u, e] == 0:
                clauses.extend([[-term] for term in terms])
            else:
                clauses.append(terms)
                clauses.extend([[-a, -b] for a, b in combinations(terms, 2)])
    # No pair of outside vertices has two common C-neighbors.
    for a, b in combinations(range(48), 2):
        common = []
        for c in range(48):
            ac, bc = tuple(sorted((a, c))), tuple(sorted((b, c)))
            if c not in (a, b) and ac in cindex and bc in cindex:
                common.append((cindex[ac], cindex[bc]))
        for (ac, bc), (ad, bd) in combinations(common, 2):
            clauses.append([-ac, -bc, -ad, -bd])
    with path.open("w") as out:
        out.write(f"p cnf {len(allowed)} {len(clauses)}\n")
        for clause in clauses:
            out.write(" ".join(map(str, clause)) + " 0\n")
    return len(allowed), len(clauses)


def emit_r_completeness_cnf(h: np.ndarray, models: list[np.ndarray], path: Path):
    """Assert the complete R ledger while excluding the supplied models."""
    pairs, rows, lower, upper = r_base_model(h)
    clauses: list[list[int]] = []
    for row, lo, hi in zip(rows, lower, upper):
        keys = sorted(row)
        for mask in range(1 << len(keys)):
            value = sum(row[key] for i, key in enumerate(keys)
                        if mask & (1 << i))
            if lo <= value <= hi:
                continue
            clauses.append([
                -(key + 1) if mask & (1 << i) else key + 1
                for i, key in enumerate(keys)
            ])
    for bits in models:
        clauses.append([-(i + 1) if bit else i + 1
                        for i, bit in enumerate(bits)])
    with path.open("w") as out:
        out.write(f"p cnf {len(pairs)} {len(clauses)}\n")
        for clause in clauses:
            out.write(" ".join(map(str, clause)) + " 0\n")
    return len(pairs), len(clauses)


def classify(parts: list[int], limit: int, show_witness: bool,
             emit_cnf_dir: Path | None = None,
             emit_r_completeness: Path | None = None):
    h = cycle_adjacency(parts)
    pairs, rvars, rsolver = make_r_solver(h)
    edge_maps = cycle_automorphism_edge_maps(parts, pairs)
    seen_orbits: set[bytes] = set()
    tested = 0
    c_alive = 0
    c_unknown = 0
    models: list[np.ndarray] = []
    while tested < limit:
        result = rsolver.check()
        if result != z3.sat:
            exhausted = result == z3.unsat
            if exhausted and emit_r_completeness is not None:
                emit_r_completeness.parent.mkdir(parents=True, exist_ok=True)
                emit_r_completeness_cnf(h, models, emit_r_completeness)
            return tested, len(seen_orbits), c_alive, c_unknown, exhausted
        model = rsolver.model()
        bits = np.array([1 if z3.is_true(model.eval(x)) else 0
                         for x in rvars], dtype=np.uint8)
        models.append(bits)
        redges = [pairs[i] for i, bit in enumerate(bits) if bit]
        ones = np.flatnonzero(bits)
        orbit_rows = np.sort(edge_maps[:, ones], axis=1)
        orbit_key = min(row.tobytes() for row in orbit_rows)
        if orbit_key in seen_orbits:
            tested += 1
            rsolver.add(z3.Or(*[x != bool(bit)
                                for x, bit in zip(rvars, bits)]))
            continue
        seen_orbits.add(orbit_key)
        if emit_cnf_dir is not None:
            emit_cnf_dir.mkdir(parents=True, exist_ok=True)
            emit_c_cnf(h, redges, emit_cnf_dir / f"r{tested + 1:03}.cnf")
        verdict, chosen, allowed_count, c4terms = c_feasible(h, redges)
        tested += 1
        if verdict == "ALIVE":
            c_alive += 1
            detail = f" R={redges} C={chosen}" if show_witness else ""
            print(f"R#{tested}/orbit#{len(seen_orbits)}: "
                  f"C4-FEASIBLE allowed={allowed_count} "
                  f"c4_terms={c4terms}{detail}", flush=True)
        elif verdict == "UNKNOWN":
            c_unknown += 1
            print(f"R#{tested}/orbit#{len(seen_orbits)}: "
                  f"C4-UNKNOWN allowed={allowed_count} "
                  f"c4_terms={c4terms}", flush=True)
        elif tested <= 10 or tested % 100 == 0:
            detail = f" R={redges}" if show_witness else ""
            print(f"R#{tested}/orbit#{len(seen_orbits)}: "
                  f"C4-DEAD allowed={allowed_count} "
                  f"c4_terms={c4terms}{detail}", flush=True)

        rsolver.add(z3.Or(*[x != bool(bit)
                            for x, bit in zip(rvars, bits)]))
    return tested, len(seen_orbits), c_alive, c_unknown, False


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("partition", choices=[*PARTITIONS, "all"])
    parser.add_argument("--limit", type=int, default=10000)
    parser.add_argument("--show-witness", action="store_true")
    parser.add_argument("--emit-cnf-dir", type=Path)
    parser.add_argument("--emit-r-completeness-cnf", type=Path)
    args = parser.parse_args()
    names = PARTITIONS if args.partition == "all" else {args.partition: PARTITIONS[args.partition]}
    for name, parts in names.items():
        print(f"=== {name} ===", flush=True)
        tested, orbits, alive, unknown, exhausted = classify(
            parts, args.limit, args.show_witness, args.emit_cnf_dir,
            args.emit_r_completeness_cnf)
        print(f"SUMMARY {name}: R_tested={tested} R_orbits={orbits} "
              f"C_alive={alive} "
              f"C_unknown={unknown} "
              f"R_exhausted={exhausted}", flush=True)


if __name__ == "__main__":
    main()
