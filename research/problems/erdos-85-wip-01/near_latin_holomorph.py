#!/usr/bin/env python3
"""Exact SAT scout for the common-coset dihedral-holomorph ansatz.

For odd q, let H be the dihedral group of order q+1.  Every within-fiber and
cross-fiber matching is required to be a permutation in Hol(H), the normalizer
of the regular H-action.  This is the precise reduced class extracted from the
checked q=7 witness by ``near_latin_q7_routing.py``.

The model requires all datum permutations to lie in Hol(H), the resulting
graph to be C4-free, and every routing factorization to be one coset of the
common regular H.  The last condition is imposed on automorphism parts: in the
unique decomposition ``p = translation * alpha``, all routes for one fiber
pair must have the same alpha.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import subprocess
import tempfile

from near_latin_q9 import Datum, objective, serializable


Permutation = tuple[int, ...]


def compose(p: Permutation, q: Permutation) -> Permutation:
    """Return p after q."""
    return tuple(p[q[x]] for x in range(len(p)))


def inverse(p: Permutation) -> Permutation:
    answer = [0] * len(p)
    for x, y in enumerate(p):
        answer[y] = x
    return tuple(answer)


def left_translation(h: int, n: int) -> Permutation:
    ha, hb = divmod(h, 2)
    return tuple(
        ((ha + (-1 if hb else 1) * a) % n) * 2 + (hb + b) % 2
        for a in range(n) for b in range(2)
    )


def automorphism_part(p: Permutation, n: int) -> Permutation:
    """The unique alpha fixing 1 such that p = left(p(1)) after alpha."""
    alpha = compose(inverse(left_translation(p[0], n)), p)
    assert alpha[0] == 0
    return alpha


def holomorph(n: int) -> list[Permutation]:
    """Hol(D_{2n}) acting on elements r^a s^b numbered 2a+b."""
    units = [u for u in range(n) if math.gcd(u, n) == 1]
    answer = set()
    for ha, hb, u, v in itertools.product(range(n), range(2), units, range(n)):
        image = []
        for a in range(n):
            for b in range(2):
                # Automorphism r↦r^u, s↦r^v s, followed by left translation
                # by r^ha s^hb.
                aa, bb = (u * a + v * b) % n, b
                image.append(((ha + (-1 if hb else 1) * aa) % n) * 2 + (hb + bb) % 2)
        answer.add(tuple(image))
    assert len(answer) == 2 * n * n * len(units)
    return sorted(answer)


def fixed_point_free_involutions(perms: list[Permutation]) -> list[Permutation]:
    return [p for p in perms if all(p[x] != x and p[p[x]] == x for x in range(len(p)))]


def paired(i: int, j: int) -> bool:
    return (i ^ 1) == j


def sat_search(q: int, timeout: int) -> tuple[str, Datum | None, dict[str, int]]:
    m, r, vertex_count = q - 1, q + 1, q * q - 1
    if r % 2:
        raise ValueError("q must be odd")
    hol = holomorph(r // 2)
    involutions = fixed_point_free_involutions(hol)

    next_var = 1
    edge_var: dict[tuple[int, int], int] = {}
    for i in range(m):
        for x in range(r):
            for y in range(x + 1, r):
                edge_var[i * r + x, i * r + y] = next_var
                next_var += 1
        for j in range(i + 1, m):
            for x in range(r):
                for y in range(r):
                    edge_var[i * r + x, j * r + y] = next_var
                    next_var += 1

    # A slot selects one holomorph permutation. Paired fiber blocks have two
    # labeled slots; an explicit collision clause makes their matchings disjoint.
    slot_candidates: dict[tuple[str, int, int, int], list[Permutation]] = {}
    for i in range(m):
        slot_candidates["within", i, i, 0] = involutions
        for j in range(i + 1, m):
            for s in range(2 if paired(i, j) else 1):
                slot_candidates["cross", i, j, s] = hol

    selector_var: dict[tuple[tuple[str, int, int, int], int], int] = {}
    for slot, candidates in slot_candidates.items():
        for index in range(len(candidates)):
            selector_var[slot, index] = next_var
            next_var += 1

    automorphisms = sorted({automorphism_part(p, r // 2) for p in hol})
    assert len(automorphisms) * r == len(hol)
    automorphism_index = {a: k for k, a in enumerate(automorphisms)}
    slot_auto_var: dict[tuple[tuple[str, int, int, int], int], int] = {}
    for slot in slot_candidates:
        for index in range(len(automorphisms)):
            slot_auto_var[slot, index] = next_var
            next_var += 1
    routing_auto_var: dict[tuple[int, int, int], int] = {}
    for i in range(m):
        for j in range(i + 1, m):
            for index in range(len(automorphisms)):
                routing_auto_var[i, j, index] = next_var
                next_var += 1

    stats = {
        "holomorph_size": len(hol),
        "within_candidates": len(involutions),
        "automorphism_group_size": len(automorphisms),
        "selection_clauses": 0,
        "automorphism_link_clauses": 0,
        "routing_cocycle_clauses": 0,
        "gauge_clauses": 0,
        "link_clauses": 0,
        "disjointness_clauses": 0,
        "c4_clauses": 0,
    }

    def edge(u: int, v: int) -> bool | int:
        if u == v:
            return False
        if u > v:
            u, v = v, u
        return edge_var.get((u, v), False)

    with tempfile.NamedTemporaryFile(mode="w+", suffix=".cnf") as cnf:
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
                raise ValueError("empty clause")
            cnf.write(" ".join(map(str, reduced)) + " 0\n")
            clause_count += 1

        # Exactly one candidate per slot.
        for slot, candidates in slot_candidates.items():
            selectors = [selector_var[slot, k] for k in range(len(candidates))]
            emit(selectors)
            stats["selection_clauses"] += 1
            for a, b in itertools.combinations(selectors, 2):
                emit([-a, -b])
                stats["selection_clauses"] += 1

        def exactly_one(lits: list[int], stat: str) -> None:
            emit(lits)
            stats[stat] += 1
            for a, b in itertools.combinations(lits, 2):
                emit([-a, -b])
                stats[stat] += 1

        # Project each selected holomorph permutation to its automorphism part.
        for slot, candidates in slot_candidates.items():
            autos = [slot_auto_var[slot, k] for k in range(len(automorphisms))]
            exactly_one(autos, "automorphism_link_clauses")
            by_auto = [[] for _ in automorphisms]
            for index, p in enumerate(candidates):
                k = automorphism_index[automorphism_part(p, r // 2)]
                selector = selector_var[slot, index]
                emit([-selector, slot_auto_var[slot, k]])
                stats["automorphism_link_clauses"] += 1
                by_auto[k].append(selector)
            for k, selectors in enumerate(by_auto):
                emit([-slot_auto_var[slot, k], *selectors])
                stats["automorphism_link_clauses"] += 1

        for i in range(m):
            for j in range(i + 1, m):
                exactly_one(
                    [routing_auto_var[i, j, k] for k in range(len(automorphisms))],
                    "routing_cocycle_clauses",
                )

        def force_route(
            i: int,
            j: int,
            left_slot: tuple[str, int, int, int],
            right_slot: tuple[str, int, int, int],
            operation,
        ) -> None:
            for a, alpha in enumerate(automorphisms):
                for b, beta in enumerate(automorphisms):
                    result = automorphism_index[operation(alpha, beta)]
                    emit([
                        -slot_auto_var[left_slot, a],
                        -slot_auto_var[right_slot, b],
                        routing_auto_var[i, j, result],
                    ])
                    stats["routing_cocycle_clauses"] += 1

        # Every channel for a fixed fiber pair must have one automorphism part.
        # Since the C4 clauses make the q+1 routes disjoint, this is equivalent
        # to saying that the routing factorization is a coset of regular H.
        for i in range(m):
            for j in range(i + 1, m):
                for s in range(2 if paired(i, j) else 1):
                    cross = ("cross", i, j, s)
                    force_route(i, j, cross, ("within", i, i, 0), compose)
                    force_route(i, j, ("within", j, j, 0), cross, compose)
                for k in range(m):
                    if k in (i, j):
                        continue
                    ik_pair = (min(i, k), max(i, k))
                    jk_pair = (min(j, k), max(j, k))
                    for a in range(2 if paired(*ik_pair) else 1):
                        for b in range(2 if paired(*jk_pair) else 1):
                            ik = ("cross", *ik_pair, a)
                            jk = ("cross", *jk_pair, b)

                            def third(alpha, beta, i=i, j=j, k=k):
                                oriented_ik = alpha if i < k else inverse(alpha)
                                oriented_jk = beta if j < k else inverse(beta)
                                return compose(inverse(oriented_jk), oriented_ik)

                            force_route(i, j, ik, jk, third)

        # Independent relabeling of fiber j by an element of Hol(H) sends a
        # cross map p_ij to g_j p_ij g_i^-1.  Along a spanning tree these
        # gauges can therefore make one selected matching the identity.  The
        # doubled slots are labeled, so use slot zero on the possible doubled
        # root edge as well.
        identity = tuple(range(r))
        identity_index = hol.index(identity)
        for j in range(1, m):
            slot = ("cross", 0, j, 0)
            emit([selector_var[slot, identity_index]])
            stats["gauge_clauses"] += 1

        supporters: dict[int, set[int]] = {e: set() for e in edge_var.values()}
        for slot, candidates in slot_candidates.items():
            kind, i, j, _ = slot
            for index, perm in enumerate(candidates):
                selector = selector_var[slot, index]
                used_edges = set()
                if kind == "within":
                    for x, y in enumerate(perm):
                        used_edges.add(int(edge(i * r + x, i * r + y)))
                else:
                    for x, y in enumerate(perm):
                        used_edges.add(int(edge(i * r + x, j * r + y)))
                for e in used_edges:
                    emit([-selector, e])
                    supporters[e].add(selector)
                    stats["link_clauses"] += 1
        for e, selectors in supporters.items():
            emit([-e, *selectors])
            stats["link_clauses"] += 1

        # The two selected permutations in a doubled block must be pointwise
        # disjoint, so their union is a simple 2-regular bipartite graph.
        for i in range(0, m, 2):
            j = i ^ 1
            left, right = ("cross", i, j, 0), ("cross", i, j, 1)
            for a, p in enumerate(hol):
                for b, s in enumerate(hol):
                    if any(p[x] == s[x] for x in range(r)):
                        emit([-selector_var[left, a], -selector_var[right, b]])
                        stats["disjointness_clauses"] += 1

        def negated(e: bool | int) -> bool | int:
            return (not e) if isinstance(e, bool) else -e

        for a, b, c, d in itertools.combinations(range(vertex_count), 4):
            for cycle in (
                ((a, b), (b, c), (c, d), (d, a)),
                ((a, b), (b, d), (d, c), (c, a)),
                ((a, c), (c, b), (b, d), (d, a)),
            ):
                before = clause_count
                emit([negated(edge(u, v)) for u, v in cycle])
                stats["c4_clauses"] += clause_count - before

        cnf.flush()
        cnf.seek(0)
        cnf.write(f"p cnf {next_var - 1:12d} {clause_count:15d}\n")
        cnf.flush()
        stats["variables"], stats["clauses"] = next_var - 1, clause_count
        try:
            result = subprocess.run(
                ["kissat", "--no-color", cnf.name],
                capture_output=True,
                text=True,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            return "UNKNOWN-TIMEOUT", None, stats

    output = result.stdout + "\n" + result.stderr
    if "s UNSATISFIABLE" in output:
        return "UNSAT", None, stats
    if "s SATISFIABLE" not in output:
        return f"UNKNOWN-RC-{result.returncode}", None, stats
    true_vars = {
        int(word)
        for line in output.splitlines() if line.startswith("v ")
        for word in line.split()[1:] if int(word) > 0
    }
    chosen: dict[tuple[str, int, int, int], Permutation] = {}
    for slot, candidates in slot_candidates.items():
        hits = [p for k, p in enumerate(candidates) if selector_var[slot, k] in true_vars]
        assert len(hits) == 1
        chosen[slot] = hits[0]
    within = [list(chosen["within", i, i, 0]) for i in range(m)]
    blocks = {}
    for i in range(m):
        for j in range(i + 1, m):
            blocks[i, j] = [
                list(chosen["cross", i, j, s])
                for s in range(2 if paired(i, j) else 1)
            ]
    datum = Datum(q, blocks, within)
    assert objective(datum) == 0
    return "SAT", datum, stats


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", type=int, default=9)
    parser.add_argument("--timeout", type=int, default=3600)
    parser.add_argument("--output")
    args = parser.parse_args()
    if args.q < 3 or args.q % 2 == 0:
        parser.error("q must be an odd integer at least 3")
    status, datum, stats = sat_search(args.q, args.timeout)
    result: dict[str, object] = {"q": args.q, "status": status, "stats": stats}
    if datum is not None:
        result |= serializable(datum) | {"C4_count": 0}
    print(json.dumps(result, sort_keys=True))
    if args.output:
        with open(args.output, "w") as stream:
            json.dump(result, stream, sort_keys=True, indent=2)
            stream.write("\n")


if __name__ == "__main__":
    main()
