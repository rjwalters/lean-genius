#!/usr/bin/env python3
"""Audit the 7-adic determinant on B1-constrained defect completions.

For each canonical propagated sixth state, a pair of ordinary vertices is a
forced defect edge when every possible common-neighbour witness is blocked,
and a forced defect nonedge when a positive witness is already present.  The
remaining defect edges are completed subject only to their exact degrees.
This deliberately weak relaxation tests how much of the determinant filter is
already visible before completing the original graph.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import subprocess
from collections import Counter
from pathlib import Path

import networkx as nx
import numpy as np

from analyze_small_high_adaptive_sixth_orbits import propagated_graph
from analyze_small_high_adaptive_sixth_root_partitions import canonical_job_ids
from analyze_small_high_adaptive_sixth_units import (
    build_falsified_occurrences,
    manifest_jobs,
    read_dimacs,
)
from audit_order49_defect_determinant import defect_matrices, determinant_expression
from audit_h16_circulant_tree_squares import bareiss_determinant


ORDINARY = tuple(range(3, 49))
ODD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)


def residual_square_root_trace_possible(
    adjacency_square: list[list[int]], target_trace: int = -7,
) -> tuple[bool, tuple[int, ...]]:
    """Test the exact rational characteristic-polynomial square-root law.

    After removing the forced zero/quadratic sector, a true ordinary
    adjacency matrix C would give

        charpoly(C_res)(t) charpoly(C_res)(-t)
          = charpoly((C_res)^2)(t^2).

    Factoring the right side over Q reduces existence to choosing one factor
    from every +/- orbit.  The returned traces are all traces obtainable by
    those choices; a true completion must contain ``target_trace``.
    """
    import sympy as sp

    x, t = sp.symbols("x t")
    characteristic = sp.Poly(sp.Matrix(adjacency_square).charpoly(x).as_expr(), x)
    forced = sp.Poly(x**2 * (x**2 - 43*x + 9), x)
    residual, remainder = sp.div(characteristic, forced)
    if remainder.as_expr() != 0:
        return False, ()
    even_lift = sp.Poly(residual.as_expr().subs(x, t**2), t)
    _content, factors = sp.factor_list(even_lift)
    factor_powers = {sp.Poly(factor, t).monic(): exponent for factor, exponent in factors}

    traces = {0}
    visited: set[sp.Poly] = set()
    for factor, exponent in factor_powers.items():
        if factor in visited:
            continue
        partner = sp.Poly(factor.as_expr().subs(t, -t), t).monic()
        partner_exponent = factor_powers.get(partner)
        if partner == factor:
            if exponent % 2:
                return False, tuple(sorted(traces))
            copies = exponent // 2
            coefficient = int(factor.all_coeffs()[1]) if factor.degree() else 0
            contribution = -copies * coefficient
            traces = {value + contribution for value in traces}
            visited.add(factor)
            continue
        if partner_exponent != exponent:
            return False, tuple(sorted(traces))
        coefficient = int(factor.all_coeffs()[1]) if factor.degree() else 0
        contribution = -exponent * coefficient
        traces = {
            value + sign * contribution
            for value in traces for sign in (-1, 1)
        }
        visited.update((factor, partner))
    possible = tuple(sorted(traces))
    return target_trace in traces, possible


def nullspace_mod_prime(matrix: list[list[int]], prime: int) -> list[list[int]]:
    rows = [[entry % prime for entry in row] for row in matrix]
    rank = 0
    pivots = []
    for column in range(len(rows[0])):
        pivot = next(
            (row for row in range(rank, len(rows)) if rows[row][column]), None
        )
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = pow(rows[rank][column], -1, prime)
        rows[rank] = [(inverse * entry) % prime for entry in rows[rank]]
        for row in range(len(rows)):
            if row == rank or not rows[row][column]:
                continue
            scale = rows[row][column]
            rows[row] = [
                (left - scale * right) % prime
                for left, right in zip(rows[row], rows[rank])
            ]
        rank += 1
        pivots.append(column)
    free = [column for column in range(len(rows[0])) if column not in pivots]
    basis = []
    for column in free:
        vector = [0] * len(rows[0])
        vector[column] = 1
        for row, pivot in enumerate(pivots):
            vector[pivot] = (-rows[row][column]) % prime
        basis.append(vector)
    return basis


def edge(u: int, v: int) -> tuple[int, int]:
    return (u, v) if u < v else (v, u)


def signed_edges(graph: nx.Graph) -> tuple[set[tuple[int, int]], set[tuple[int, int]]]:
    positive = set()
    negative = set()
    for u, v, data in graph.edges(data=True):
        (positive if data["state"] == "1" else negative).add(edge(u, v))
    return positive, negative


def defect_smt(
    graph: nx.Graph, blocked: list[frozenset[tuple[int, int]]],
    ungrounded_components: int, min_ungrounded_size: int,
    enforce_high_kernel: bool, enforce_high_eigenvectors: bool,
    enforce_high_affine: bool,
) -> tuple[str, list[tuple[int, int]]]:
    positive, negative = signed_edges(graph)
    pairs = [(u, v) for u in ORDINARY for v in ORDINARY if u < v]
    lines = [
        "(set-logic QF_LIA)",
    ]
    lines.extend(f"(declare-const d_{u}_{v} Bool)" for u, v in pairs)
    for component in range(ungrounded_components):
        lines.extend(
            f"(declare-const s_{component}_{u} Bool)" for u in ORDINARY
        )

    for u, v in pairs:
        witnesses = [w for w in range(49) if w not in (u, v)]
        if any(edge(u, w) in positive and edge(v, w) in positive for w in witnesses):
            lines.append(f"(assert (not d_{u}_{v}))")
        elif all(edge(u, w) in negative or edge(v, w) in negative for w in witnesses):
            lines.append(f"(assert d_{u}_{v})")

    for u in ORDINARY:
        high_incidence = sum(edge(root, u) in positive for root in range(3))
        target = 6 - high_incidence
        terms = [
            f"(ite d_{min(u, v)}_{max(u, v)} 1 0)"
            for v in ORDINARY
            if v != u
        ]
        lines.append(f"(assert (= (+ {' '.join(terms)}) {target}))")
        if high_incidence:
            for component in range(ungrounded_components):
                lines.append(f"(assert (not s_{component}_{u}))")
    if enforce_high_kernel or enforce_high_eigenvectors:
        for left in (0, 1):
            vector = {
                u: int(edge(left, u) in positive) - int(edge(2, u) in positive)
                for u in ORDINARY
            }
            for u in ORDINARY:
                terms = [str(6 * vector[u])]
                terms.extend(
                    f"(ite d_{min(u, v)}_{max(u, v)} {-vector[v]} 0)"
                    for v in ORDINARY if v != u and vector[v]
                )
                expression = f"(+ {' '.join(terms)})"
                if enforce_high_eigenvectors:
                    lines.append(f"(assert (= {expression} {7 * vector[u]}))")
                else:
                    lines.append(f"(assert (= (mod {expression} 7) 0))")
    if enforce_high_affine:
        for root in range(3):
            incidence = {
                u: int(edge(root, u) in positive) for u in ORDINARY
            }
            for u in ORDINARY:
                terms = [
                    f"(ite d_{min(u, v)}_{max(u, v)} 1 0)"
                    for v in ORDINARY if v != u and incidence[v]
                ]
                lines.append(
                    f"(assert (= (+ {' '.join(terms)}) {1 - incidence[u]}))"
                )
    for component in range(ungrounded_components):
        lines.append("(assert (or " + " ".join(
            f"s_{component}_{u}" for u in ORDINARY
        ) + "))")
        if min_ungrounded_size:
            lines.append("(assert (>= (+ " + " ".join(
                f"(ite s_{component}_{u} 1 0)" for u in ORDINARY
            ) + f") {min_ungrounded_size}))")
        for u, v in pairs:
            # A selected union of components has no defect edge across its cut.
            lines.append(
                f"(assert (or (= s_{component}_{u} s_{component}_{v}) "
                f"(not d_{u}_{v})))"
            )
    for left in range(ungrounded_components):
        for right in range(left + 1, ungrounded_components):
            for u in ORDINARY:
                lines.append(f"(assert (not (and s_{left}_{u} s_{right}_{u})))")
    for previous in blocked:
        difference = [
            f"(not d_{u}_{v})" if (u, v) in previous else f"d_{u}_{v}"
            for u, v in pairs
        ]
        lines.append(f"(assert (or {' '.join(difference)}))")
    lines.extend([
        "(check-sat)",
        "(get-value (" + " ".join(f"d_{u}_{v}" for u, v in pairs) + "))",
    ])
    return "\n".join(lines) + "\n", pairs


def solve_defect(
    graph: nx.Graph, blocked: list[frozenset[tuple[int, int]]], timeout: int,
    ungrounded_components: int, min_ungrounded_size: int,
    enforce_high_kernel: bool, enforce_high_eigenvectors: bool,
    enforce_high_affine: bool,
) -> tuple[nx.Graph, frozenset[tuple[int, int]]] | None:
    smt, pairs = defect_smt(
        graph, blocked, ungrounded_components, min_ungrounded_size,
        enforce_high_kernel, enforce_high_eigenvectors,
        enforce_high_affine,
    )
    completed = subprocess.run(
        ["z3", "-in", f"-T:{timeout}"], input=smt, text=True,
        capture_output=True, check=False,
    )
    if completed.stdout.startswith("unsat"):
        return None
    if not completed.stdout.startswith("sat"):
        raise RuntimeError(completed.stdout.strip() or completed.stderr.strip())
    values = {
        (int(u), int(v)): value == "true"
        for u, v, value in re.findall(r"\(d_(\d+)_(\d+)\s+(true|false)\)", completed.stdout)
    }
    if len(values) != len(pairs):
        raise AssertionError(f"parsed {len(values)} of {len(pairs)} defect variables")
    result = nx.Graph()
    result.add_nodes_from(range(len(ORDINARY)))
    result.add_edges_from((u - 3, v - 3) for (u, v), present in values.items() if present)
    signature = frozenset(pair for pair, present in values.items() if present)
    return result, signature


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--orbits", type=Path, required=True)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--completions", type=int, default=1)
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--require-ungrounded-component", action="store_true")
    parser.add_argument("--ungrounded-components", type=int, default=0)
    parser.add_argument("--min-ungrounded-size", type=int, default=0)
    parser.add_argument("--enforce-high-kernel", action="store_true")
    parser.add_argument("--enforce-high-eigenvectors", action="store_true")
    parser.add_argument("--enforce-high-affine", action="store_true")
    parser.add_argument("--audit-square-root-charpoly", action="store_true")
    parser.add_argument("--print-values", action="store_true")
    args = parser.parse_args()
    if args.ungrounded_components < 0:
        parser.error("--ungrounded-components must be nonnegative")
    if args.min_ungrounded_size < 0:
        parser.error("--min-ungrounded-size must be nonnegative")
    ungrounded_components = max(
        args.ungrounded_components, int(args.require_ungrounded_component)
    )

    manifest = json.loads(args.manifest.read_text())
    orbit_report = json.loads(args.orbits.read_text())
    jobs = dict(manifest_jobs(manifest))
    job_ids = canonical_job_ids(orbit_report)
    if args.limit is not None:
        job_ids = job_ids[:args.limit]
    bases = {Path(leaf["base"]) for leaf in manifest["leaves"].values()}
    if len(bases) != 1:
        raise ValueError("expected one shared base CNF")
    _variables, clauses = read_dimacs(next(iter(bases)))
    occurrences = build_falsified_occurrences(clauses)
    base_units = tuple(clause[0] for clause in clauses if len(clause) == 1)

    counts: Counter[str] = Counter()
    residues: Counter[int] = Counter()
    ungrounded_patterns: Counter[tuple[int, ...]] = Counter()
    mod_seven_nullities: Counter[tuple[int, bool]] = Counter()
    mod_seven_kernel_signatures: Counter[
        tuple[int, bool, tuple[tuple[int, int], ...]]
    ] = Counter()
    lifted_forest_terms: Counter[tuple[int, int, int]] = Counter()
    quotient_nonresidue_primes: Counter[int | str] = Counter()
    root_defect_balance_profiles: Counter[
        tuple[bool, tuple[tuple[int, int], ...]]
    ] = Counter()
    empty_block_profiles: Counter[tuple[int, tuple[tuple[int, int], ...]]] = Counter()
    normalized_residual_mod_sixteen: Counter[int | str] = Counter()
    square_root_charpoly_profiles: Counter[tuple[bool, tuple[int, ...]]] = Counter()
    normalized_residual_three_adic: Counter[tuple[int, int] | str] = Counter()
    ordinary_adjacency_square_inertia: Counter[int] = Counter()
    ordinary_adjacency_square_determinants: Counter[tuple[str, bool]] = Counter()
    pairpoint_adjacency_profiles: Counter[
        tuple[tuple[str, str, str], int, tuple[tuple[int, int], ...]]
    ] = Counter()
    for job_id in job_ids:
        state = propagated_graph(clauses, occurrences, base_units, jobs[job_id])
        blocked: list[frozenset[tuple[int, int]]] = []
        for completion_index in range(args.completions):
            try:
                solved = solve_defect(
                    state, blocked, args.timeout, ungrounded_components,
                    args.min_ungrounded_size, args.enforce_high_kernel,
                    args.enforce_high_eigenvectors,
                    args.enforce_high_affine,
                )
            except RuntimeError as error:
                if str(error) != "timeout":
                    raise
                counts["timeout"] += 1
                break
            if solved is None:
                counts["unsat"] += 1
                break
            defect, signature = solved
            blocked.append(signature)
            counts["sat"] += 1
            positive, _negative = signed_edges(state)
            root_neighborhoods = [
                {u for u in ORDINARY if edge(root, u) in positive}
                for root in range(3)
            ]
            pairpoints = [
                next(iter(root_neighborhoods[left] & root_neighborhoods[right]))
                for left, right in ((0, 1), (0, 2), (1, 2))
            ]
            pairpoint_states = tuple(
                "1" if edge(pairpoints[left], pairpoints[right]) in positive else
                "0" if edge(pairpoints[left], pairpoints[right]) in _negative else
                "?"
                for left, right in ((0, 1), (0, 2), (1, 2))
            )
            known_pairpoint_edges = pairpoint_states.count("1")
            inferred_pairpoint_o_incidence = 6 + 2 * known_pairpoint_edges
            inferred_o_profile = tuple(sorted((
                (4, 25 - inferred_pairpoint_o_incidence),
                (5, inferred_pairpoint_o_incidence),
            )))
            pairpoint_adjacency_profiles[
                (pairpoint_states, 50 + inferred_pairpoint_o_incidence // 2,
                 inferred_o_profile)
            ] += 1
            balances = [
                tuple(
                    sum(defect.has_edge(v - 3, u - 3) for u in neighborhood)
                    + int(v in neighborhood)
                    for v in ORDINARY
                )
                for neighborhood in root_neighborhoods
            ]
            balanced = balances[0] == balances[1] == balances[2]
            profile = tuple(sorted(Counter(balances[0]).items()))
            root_defect_balance_profiles[(balanced, profile)] += 1
            empty = {
                v for v in ORDINARY
                if not any(v in neighborhood for neighborhood in root_neighborhoods)
            }
            empty_degrees = Counter(
                sum(defect.has_edge(v - 3, u - 3) for u in empty)
                for v in empty
            )
            empty_edges = defect.subgraph({v - 3 for v in empty}).number_of_edges()
            empty_block_profiles[(empty_edges, tuple(sorted(empty_degrees.items())))] += 1
            incidence_matrix = np.array([
                [int(v in neighborhood) for neighborhood in root_neighborhoods]
                for v in ORDINARY
            ], dtype=float)
            defect_matrix = nx.to_numpy_array(
                defect, nodelist=range(len(ORDINARY)), dtype=float
            )
            adjacency_square = (
                6 * np.eye(len(ORDINARY))
                + np.ones((len(ORDINARY), len(ORDINARY)))
                - incidence_matrix @ incidence_matrix.T
                - defect_matrix
            )
            eigenvalues = np.linalg.eigvalsh(adjacency_square)
            ordinary_adjacency_square_inertia[
                int(np.count_nonzero(eigenvalues < -1e-8))
            ] += 1
            adjacency_square_determinant = bareiss_determinant(
                adjacency_square.astype(int).tolist()
            )
            if args.audit_square_root_charpoly:
                square_root_charpoly_profiles[
                    residual_square_root_trace_possible(
                        adjacency_square.astype(int).tolist()
                    )
                ] += 1
            ungrounded = sorted(
                len(component)
                for component in nx.connected_components(defect)
                if all(
                    not any(edge(root, vertex + 3) in positive for root in range(3))
                    for vertex in component
                )
            )
            ungrounded_patterns[tuple(ungrounded)] += 1
            if nx.is_connected(defect):
                counts["connected"] += 1
            value = determinant_expression(defect)
            lap, _bordered = defect_matrices(defect)
            kernel = nullspace_mod_prime(lap, 7)
            nullity = len(kernel)
            mod_seven_nullities[(nullity, value % 49 == 0)] += 1
            signature = tuple(
                (sum(entry != 0 for entry in vector), sum(vector) % 7)
                for vector in kernel
            )
            mod_seven_kernel_signatures[(nullity, value % 49 == 0, signature)] += 1
            if value % 49 == 0:
                _lap, bordered = defect_matrices(defect)
                det_lap = bareiss_determinant(lap)
                forest_green = -bareiss_determinant(bordered)
                lifted_forest_terms[(nullity, det_lap % 49, forest_green % 7)] += 1
                if args.print_values:
                    print(
                        "value", job_id, completion_index,
                        "detL", det_lap, "K", forest_green,
                        "T", value, "S", value // 49,
                    )
            residues[value % 49] += 1
            if value % 49:
                continue
            counts["divisible_by_49"] += 1
            quotient = value // 49
            if quotient % (46 * 46) == 0:
                normalized_residual = quotient // (46 * 46)
                normalized_residual_mod_sixteen[normalized_residual % 16] += 1
                valuation = 0
                residual_part = abs(normalized_residual)
                while residual_part and residual_part % 3 == 0:
                    valuation += 1
                    residual_part //= 3
                normalized_residual_three_adic[
                    (normalized_residual % 3, valuation)
                ] += 1
                determinant_class = (
                    "zero" if adjacency_square_determinant == 0 else
                    "positive_square" if adjacency_square_determinant > 0
                        and math.isqrt(adjacency_square_determinant) ** 2
                            == adjacency_square_determinant else
                    "nonsquare"
                )
                ordinary_adjacency_square_determinants[
                    (determinant_class,
                     adjacency_square_determinant == normalized_residual)
                ] += 1
            else:
                normalized_residual_mod_sixteen["nonintegral"] += 1
                normalized_residual_three_adic["nonintegral"] += 1
            if quotient >= 0 and math.isqrt(quotient) ** 2 == quotient:
                counts["forty_nine_times_square"] += 1
            else:
                obstruction = next(
                    (prime for prime in ODD_PRIMES
                     if pow(quotient % prime, (prime - 1) // 2, prime) == prime - 1),
                    "none",
                )
                quotient_nonresidue_primes[obstruction] += 1

    print("jobs", len(job_ids), "completions", args.completions, dict(counts))
    print("residues_mod_49", dict(sorted(residues.items())))
    print("ungrounded_component_sizes", dict(sorted(ungrounded_patterns.items())))
    print("mod7_nullity_by_mod49", dict(sorted(mod_seven_nullities.items())))
    print("mod7_kernel_support_sum_by_mod49", dict(
        sorted(mod_seven_kernel_signatures.items())
    ))
    print("lifted_nullity_detL_mod49_K_mod7", dict(sorted(lifted_forest_terms.items())))
    print("quotient_first_nonresidue_prime", dict(quotient_nonresidue_primes))
    print("root_defect_balance_profiles", dict(sorted(root_defect_balance_profiles.items())))
    print("empty_block_profiles", dict(sorted(empty_block_profiles.items())))
    print("normalized_residual_mod16", dict(normalized_residual_mod_sixteen))
    if args.audit_square_root_charpoly:
        print("square_root_charpoly_profiles", dict(square_root_charpoly_profiles))
    print("normalized_residual_mod3_valuation", dict(normalized_residual_three_adic))
    print("ordinary_adjacency_square_negative_eigenvalues", dict(
        ordinary_adjacency_square_inertia
    ))
    print("ordinary_adjacency_square_det_class_eq_residual", dict(
        ordinary_adjacency_square_determinants
    ))
    print("pairpoint_states_inferred_C_empty_edges_degrees", dict(
        pairpoint_adjacency_profiles
    ))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
