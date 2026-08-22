#!/usr/bin/env python3
"""Fit invariant antisymmetric matching potentials for the q=9 B.3 horn.

The basic potential class only sees ordered row types and U1-support
intersection size.  Optional modes refine a row type by its candidate count,
the total or pair-collision count of its selected-label loads, or their full
multiset.  A cutting-plane LP minimizes
the worst (over outer witnesses) sum of the 47 local maximum-weight matching
values.  The matching oracle is an exact binary MILP, so convergence with a
negative objective certifies (12h) for every supplied witness.  Objective
zero says that the selected invariant class is insufficient.
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter
from itertools import combinations

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import lil_matrix

from q9_b0_residual_defect_sat import N, N_TRIPLE, N_U1, make_outer_seed


TYPE_NAMES = ("triple", "hole", "pair-low", "pair-high", "pair-other")


def row_types(branch: int, colors: tuple[int, int]) -> list[int]:
    holes = 2 if branch == 3 else 4
    regular = N_TRIPLE - holes
    result = []
    for u in range(N):
        if u < regular:
            result.append(0)
        elif u < N_TRIPLE:
            result.append(1)
        else:
            missing = (u - N_TRIPLE) // 7
            result.append(2 + colors.index(missing) if missing in colors else 4)
    return result


def feature_index() -> dict[tuple[int, int, int], int]:
    return {
        (a, b, overlap): i
        for i, (a, b, overlap) in enumerate(
            (x for a in range(5) for b in range(a + 1, 5)
             for overlap in (0, 1) for x in [(a, b, overlap)])
        )
    }


FEATURES = feature_index()


def coefficient_bounds() -> list[tuple[float, float]]:
    """Use the Farkas sign restriction on tagged incoming-cap prices."""
    inverse = {i: key for key, i in FEATURES.items()}
    return [
        (0, 1) if isinstance(inverse[i], tuple)
        and inverse[i] and inverse[i][0] == "mu" else (-1, 1)
        for i in range(len(FEATURES))
    ]


def sparse_coefficient_bounds() -> list[tuple[float | None, float | None]]:
    inverse = {i: key for key, i in FEATURES.items()}
    return [
        (0, None) if isinstance(inverse[i], tuple)
        and inverse[i] and inverse[i][0] == "mu" else (None, None)
        for i in range(len(FEATURES))
    ]


def edge_vector(types: list[int], blocks: list[set[int]], u: int,
                v: int) -> np.ndarray:
    answer = np.zeros(len(FEATURES))
    a, b = types[u], types[v]
    if a == b:
        return answer
    overlap = len(blocks[u] & blocks[v])
    if overlap > 1:
        raise RuntimeError("outer supports are not linear")
    key = (min(a, b), max(a, b), overlap)
    answer[FEATURES[key]] = 1 if a < b else -1
    return answer


def instance(branch: int, seed: dict, colors: tuple[int, int]) -> dict:
    blocks = [set(block) for block in seed["blocks"]]
    k_neighbors = [set() for _ in range(N_U1)]
    for a, b in seed["k_edges"]:
        k_neighbors[a].add(b)
        k_neighbors[b].add(a)
    core = [set().union(*(k_neighbors[b] for b in block)) for block in blocks]
    selected = set(range(8 * colors[0], 8 * colors[0] + 8)) | set(
        range(8 * colors[1], 8 * colors[1] + 8)
    )
    types = row_types(branch, colors)
    holes = 2 if branch == 3 else 4
    degree = np.array([5 if u < N_TRIPLE - holes else 6 for u in range(N)])
    candidates = []
    vectors = []
    labels = []
    for t in range(N):
        cs, vs, ls = [], [], []
        for u in range(N):
            if u == t or blocks[u] & core[t] or blocks[t] & core[u]:
                continue
            cs.append(u)
            vs.append(edge_vector(types, blocks, t, u))
            ls.append(blocks[u] & selected)
        candidates.append(cs)
        vectors.append(np.array(vs))
        labels.append(ls)
    return {"degree": degree, "candidates": candidates,
            "vectors": vectors, "labels": labels, "blocks": blocks,
            "types": types, "selected": selected}


def refine_features(instances: list[dict], mode: str) -> None:
    """Replace basic vectors by vectors for a finer vertex signature.

    Every refined mode retains candidate count.  ``collisions`` adds
    sum_b binom(load_b, 2), the number of pairs of eligible candidates which
    conflict at a selected U1 label.
    """
    global FEATURES
    if mode == "farkas-curl":
        selected_labels = sorted({b for data in instances
                                  for b in data["selected"]})
        keys = ([('alpha', t) for t in range(N)]
                + [('mu', t, b) for t in range(N)
                   for b in selected_labels])
        FEATURES = {key: i for i, key in enumerate(keys)}
        for data in instances:
            vectors = []
            for t in range(N):
                row_vectors = []
                own_support = data["blocks"][t] & data["selected"]
                for j, u in enumerate(data["candidates"][t]):
                    vector = np.zeros(len(FEATURES))
                    vector[FEATURES[('alpha', t)]] += 1
                    vector[FEATURES[('alpha', u)]] -= 1
                    for b in data["labels"][t][j]:
                        vector[FEATURES[('mu', t, b)]] += 1
                    for b in own_support:
                        vector[FEATURES[('mu', u, b)]] -= 1
                    row_vectors.append(vector)
                vectors.append(np.array(row_vectors))
            data["vectors"] = vectors
        return
    if mode == "row-fiber-curl":
        selected_labels = sorted({b for data in instances
                                  for row in data["labels"] for support in row
                                  for b in support})
        FEATURES = {
            (t, b): i for i, (t, b) in enumerate(
                (x for t in range(N) for b in selected_labels
                 for x in [(t, b)])
            )
        }
        for data in instances:
            vectors = []
            for t in range(N):
                row_vectors = []
                own_support = data["blocks"][t] & data["selected"]
                for j, u in enumerate(data["candidates"][t]):
                    vector = np.zeros(len(FEATURES))
                    for b in data["labels"][t][j]:
                        vector[FEATURES[(t, b)]] += 1
                    for b in own_support:
                        vector[FEATURES[(u, b)]] -= 1
                    row_vectors.append(vector)
                vectors.append(np.array(row_vectors))
            data["vectors"] = vectors
        return
    if mode == "free-gradient":
        FEATURES = {t: t for t in range(N)}
        for data in instances:
            vectors = []
            for t in range(N):
                row_vectors = []
                for u in data["candidates"][t]:
                    vector = np.zeros(N)
                    vector[t] = 1
                    vector[u] -= 1
                    row_vectors.append(vector)
                vectors.append(np.array(row_vectors))
            data["vectors"] = vectors
        return
    if mode == "gradient-collisions":
        row_data = []
        signatures = set()
        for data in instances:
            stats = []
            for t in range(N):
                loads = Counter(b for support in data["labels"][t]
                                for b in support)
                collisions = sum(x * (x - 1) // 2 for x in loads.values())
                signature = (data["types"][t], len(data["candidates"][t]),
                             collisions)
                stats.append(signature)
                signatures.add(signature)
            row_data.append(stats)
        FEATURES = {
            (overlap, signature): i
            for i, (overlap, signature) in enumerate(
                (x for overlap in (0, 1) for signature in sorted(signatures)
                 for x in [(overlap, signature)])
            )
        }
        for data, stats in zip(instances, row_data):
            vectors = []
            for t in range(N):
                row_vectors = []
                for u in data["candidates"][t]:
                    overlap = len(data["blocks"][t] & data["blocks"][u])
                    vector = np.zeros(len(FEATURES))
                    vector[FEATURES[(overlap, stats[t])]] += 1
                    vector[FEATURES[(overlap, stats[u])]] -= 1
                    row_vectors.append(vector)
                vectors.append(np.array(row_vectors))
            data["vectors"] = vectors
        return
    if mode == "collision-differences":
        row_data = []
        keys = set()
        for data in instances:
            stats = []
            for t in range(N):
                loads = Counter(b for support in data["labels"][t]
                                for b in support)
                collisions = sum(x * (x - 1) // 2 for x in loads.values())
                stats.append((data["types"][t], len(data["candidates"][t]),
                              collisions))
            row_data.append(stats)
            for t in range(N):
                for u in data["candidates"][t]:
                    overlap = len(data["blocks"][t] & data["blocks"][u])
                    raw = (stats[t][0], stats[u][0],
                           stats[t][1] - stats[u][1],
                           stats[t][2] - stats[u][2], overlap)
                    reverse = (raw[1], raw[0], -raw[2], -raw[3], overlap)
                    if raw != reverse:
                        keys.add(min(raw, reverse))
        FEATURES = {key: i for i, key in enumerate(sorted(keys))}
        for data, stats in zip(instances, row_data):
            vectors = []
            for t in range(N):
                row_vectors = []
                for u in data["candidates"][t]:
                    overlap = len(data["blocks"][t] & data["blocks"][u])
                    raw = (stats[t][0], stats[u][0],
                           stats[t][1] - stats[u][1],
                           stats[t][2] - stats[u][2], overlap)
                    reverse = (raw[1], raw[0], -raw[2], -raw[3], overlap)
                    vector = np.zeros(len(FEATURES))
                    if raw != reverse:
                        vector[FEATURES[min(raw, reverse)]] = (
                            1 if raw < reverse else -1
                        )
                    row_vectors.append(vector)
                vectors.append(np.array(row_vectors))
            data["vectors"] = vectors
        return
    if mode == "bilinear-collisions":
        coordinate_pairs = list(combinations(range(7), 2))
        FEATURES = {
            (overlap, i, j): k
            for k, (overlap, (i, j)) in enumerate(
                (x for overlap in (0, 1) for pair in coordinate_pairs
                 for x in [(overlap, pair)])
            )
        }
        for data in instances:
            row_features = []
            for t in range(N):
                loads = Counter(b for support in data["labels"][t]
                                for b in support)
                collisions = sum(x * (x - 1) // 2 for x in loads.values())
                row_features.append(np.array(
                    [int(data["types"][t] == i) for i in range(5)]
                    + [len(data["candidates"][t]), collisions], dtype=float
                ))
            vectors = []
            for t in range(N):
                row_vectors = []
                for u in data["candidates"][t]:
                    overlap = len(data["blocks"][t] & data["blocks"][u])
                    vector = np.zeros(len(FEATURES))
                    for i, j in coordinate_pairs:
                        vector[FEATURES[(overlap, i, j)]] = (
                            row_features[t][i] * row_features[u][j]
                            - row_features[t][j] * row_features[u][i]
                        )
                    row_vectors.append(vector)
                vectors.append(np.array(row_vectors))
            data["vectors"] = vectors
        return
    signatures = []
    keys = set()
    for data in instances:
        row_signatures = []
        for t in range(N):
            signature = (data["types"][t], len(data["candidates"][t]))
            if mode == "matching-capacity":
                count = len(data["candidates"][t])
                caps = lil_matrix((N_U1, count))
                for j, support in enumerate(data["labels"][t]):
                    for b in support:
                        caps[b, j] = 1
                result = milp(
                    c=-np.ones(count), integrality=np.ones(count),
                    bounds=Bounds(np.zeros(count), np.ones(count)),
                    constraints=LinearConstraint(
                        caps.tocsr(), np.zeros(N_U1), np.ones(N_U1)
                    ), options={"time_limit": 30},
                )
                if not result.success:
                    raise RuntimeError(f"capacity oracle failed: {result.message}")
                signature += (round(-result.fun),)
            elif mode in ("total-load", "collisions", "load-shape",
                        "load-profile"):
                loads = Counter(b for support in data["labels"][t]
                                for b in support)
                if mode == "total-load":
                    signature += (sum(loads.values()),)
                elif mode == "collisions":
                    signature += (sum(x * (x - 1) // 2
                                      for x in loads.values()),)
                elif mode == "load-shape":
                    signature += (max(loads.values(), default=0),
                                  sum(x >= 2 for x in loads.values()))
                else:
                    signature += (tuple(sorted(loads.values())),)
            row_signatures.append(signature)
        signatures.append(row_signatures)
        for t in range(N):
            for u in data["candidates"][t]:
                if row_signatures[t] != row_signatures[u]:
                    keys.add((min(row_signatures[t], row_signatures[u]),
                              max(row_signatures[t], row_signatures[u]),
                              len(data["blocks"][t] & data["blocks"][u])))
    FEATURES = {key: i for i, key in enumerate(sorted(keys))}
    for data, row_signatures in zip(instances, signatures):
        vectors = []
        for t in range(N):
            row_vectors = []
            for u in data["candidates"][t]:
                vector = np.zeros(len(FEATURES))
                a, b = row_signatures[t], row_signatures[u]
                if a != b:
                    key = (min(a, b), max(a, b),
                           len(data["blocks"][t] & data["blocks"][u]))
                    vector[FEATURES[key]] = 1 if a < b else -1
                row_vectors.append(vector)
            vectors.append(np.array(row_vectors))
        data["vectors"] = vectors


def oracle(data: dict, row: int, theta: np.ndarray) -> tuple[float, np.ndarray] | None:
    vectors = data["vectors"][row]
    count = len(vectors)
    if count == 0:
        return None
    constraints = lil_matrix((1 + N_U1, count))
    constraints[0, :] = 1
    for j, support in enumerate(data["labels"][row]):
        for b in support:
            constraints[1 + b, j] = 1
    d = data["degree"][row]
    result = milp(
        c=-(vectors @ theta), integrality=np.ones(count),
        bounds=Bounds(np.zeros(count), np.ones(count)),
        constraints=LinearConstraint(
            constraints.tocsr(), np.r_[d, np.zeros(N_U1)],
            np.r_[d, np.ones(N_U1)]
        ), options={"time_limit": 30},
    )
    if result.status == 2:
        return None
    if not result.success:
        raise RuntimeError(f"matching oracle failed: {result.message}")
    chosen = result.x > .5
    vector = vectors[chosen].sum(axis=0)
    return float(vector @ theta), vector


def fit(instances: list[dict], max_rounds: int) -> tuple[str, float, np.ndarray, int]:
    nf = len(FEATURES)
    nr = len(instances) * N
    z_index = nf + nr
    cuts: list[tuple[int, np.ndarray]] = []
    zero = np.zeros(nf)
    for i, data in enumerate(instances):
        for row in range(N):
            answer = oracle(data, row, zero)
            if answer is None:
                return "local-hall", float("nan"), zero, 0
            cuts.append((i * N + row, answer[1]))

    theta = zero
    objective = 0.0
    for round_number in range(1, max_rounds + 1):
        # q_(instance,row) upper-bounds every matching value; z upper-bounds
        # the sum of q over rows in each instance.
        aub = lil_matrix((len(cuts) + len(instances), z_index + 1))
        bub = np.zeros(aub.shape[0])
        for k, (ir, vector) in enumerate(cuts):
            aub[k, :nf] = vector
            aub[k, nf + ir] = -1
        for i in range(len(instances)):
            k = len(cuts) + i
            aub[k, nf + i * N:nf + (i + 1) * N] = 1
            aub[k, z_index] = -1
        c = np.zeros(z_index + 1)
        c[z_index] = 1
        result = linprog(
            c, A_ub=aub.tocsr(), b_ub=bub,
            bounds=coefficient_bounds() + [(None, None)] * (nr + 1),
            method="highs",
        )
        if not result.success:
            raise RuntimeError(f"master LP failed: {result.message}")
        theta = result.x[:nf]
        objective = result.x[z_index]
        violations = 0
        q = result.x[nf:nf + nr]
        for i, data in enumerate(instances):
            for row in range(N):
                answer = oracle(data, row, theta)
                if answer is None:
                    return "local-hall", float("nan"), theta, round_number
                value, vector = answer
                ir = i * N + row
                if value > q[ir] + 1e-7:
                    cuts.append((ir, vector))
                    violations += 1
        print(f"round={round_number} objective={objective:.9g} new_cuts={violations}")
        if violations == 0:
            return "separates" if objective < -1e-7 else "no-separation", objective, theta, round_number
    return "round-limit", objective, theta, max_rounds


def fit_sparse(instances: list[dict], max_rounds: int) -> tuple[str, float, np.ndarray, int]:
    """Minimize coefficient L1 norm subject to margin at most -1."""
    nf = len(FEATURES)
    nr = len(instances) * N
    abs_start = nf + nr
    cuts: list[tuple[int, np.ndarray]] = []
    zero = np.zeros(nf)
    for i, data in enumerate(instances):
        for row in range(N):
            answer = oracle(data, row, zero)
            if answer is None:
                return "local-hall", float("nan"), zero, 0
            cuts.append((i * N + row, answer[1]))
    theta = zero
    norm = float("nan")
    for round_number in range(1, max_rounds + 1):
        rows = len(cuts) + len(instances) + 2 * nf
        aub = lil_matrix((rows, abs_start + nf))
        bub = np.zeros(rows)
        for k, (ir, vector) in enumerate(cuts):
            aub[k, :nf] = vector
            aub[k, nf + ir] = -1
        offset = len(cuts)
        for i in range(len(instances)):
            aub[offset + i, nf + i * N:nf + (i + 1) * N] = 1
            bub[offset + i] = -1
        offset += len(instances)
        for i in range(nf):
            aub[offset + 2 * i, i] = 1
            aub[offset + 2 * i, abs_start + i] = -1
            aub[offset + 2 * i + 1, i] = -1
            aub[offset + 2 * i + 1, abs_start + i] = -1
        objective = np.r_[np.zeros(abs_start), np.ones(nf)]
        result = linprog(
            objective, A_ub=aub.tocsr(), b_ub=bub,
            bounds=(sparse_coefficient_bounds()
                    + [(None, None)] * nr + [(0, None)] * nf),
            method="highs",
        )
        if result.status == 2:
            return "no-separation", float("inf"), zero, round_number
        if not result.success:
            raise RuntimeError(f"sparse master LP failed: {result.message}")
        theta = result.x[:nf]
        norm = result.fun
        q = result.x[nf:nf + nr]
        violations = 0
        for i, data in enumerate(instances):
            for row in range(N):
                answer = oracle(data, row, theta)
                if answer is None:
                    return "local-hall", float("nan"), theta, round_number
                value, vector = answer
                ir = i * N + row
                if value > q[ir] + 1e-7:
                    cuts.append((ir, vector))
                    violations += 1
        print(f"round={round_number} l1={norm:.9g} new_cuts={violations}")
        if violations == 0:
            return "separates", norm, theta, round_number
    return "round-limit", norm, theta, max_rounds


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=int, default=1)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument("--max-rounds", type=int, default=100)
    parser.add_argument("--individual", action="store_true",
                        help="fit each locally feasible instance separately")
    parser.add_argument("--sparse", action="store_true",
                        help="minimize coefficient L1 norm at margin -1")
    parser.add_argument("--features", choices=("basic", "candidate-count",
                                                "total-load", "collisions",
                                                "load-shape", "load-profile",
                                                "matching-capacity",
                                                "bilinear-collisions",
                                                "collision-differences",
                                                "gradient-collisions",
                                                "free-gradient",
                                                "row-fiber-curl",
                                                "farkas-curl"),
                        default="basic")
    args = parser.parse_args()
    data = []
    data_labels = []
    hall_labels = []
    for branch in (3, 4):
        for seed_number in range(args.seeds):
            seed = make_outer_seed(branch, args.timeout_seconds * 1000, seed_number)
            for colors in combinations(range(3), 2):
                candidate = instance(branch, seed, colors)
                bad_rows = [row for row in range(N)
                            if oracle(candidate, row, np.zeros(len(FEATURES))) is None]
                if bad_rows:
                    hall_labels.append((branch, seed_number, colors, bad_rows))
                else:
                    data.append(candidate)
                    data_labels.append((branch, seed_number, colors))
    for branch, seed_number, colors, bad_rows in hall_labels:
        print(f"local_hall branch={branch} seed={seed_number} "
              f"colors={colors} rows={bad_rows}")
    if not data:
        print(f"instances=0 local_hall_instances={len(hall_labels)}")
        return 0
    if args.features != "basic":
        refine_features(data, args.features)
        print(f"feature_mode={args.features} feature_count={len(FEATURES)}")
    if args.individual:
        for label, candidate in zip(data_labels, data):
            fitter = fit_sparse if args.sparse else fit
            status, objective, _, rounds = fitter([candidate], args.max_rounds)
            branch, seed_number, colors = label
            print(f"individual branch={branch} seed={seed_number} colors={colors} "
                  f"status={status} objective={objective:.9g} rounds={rounds}")
        return 0
    fitter = fit_sparse if args.sparse else fit
    status, objective, theta, rounds = fitter(data, args.max_rounds)
    print(f"instances={len(data)} local_hall_instances={len(hall_labels)} "
          f"status={status} objective={objective:.9g} rounds={rounds}")
    if args.features == "basic":
        for feature, i in FEATURES.items():
            if abs(theta[i]) > 1e-7:
                a, b, overlap = feature
                print(f"theta[{TYPE_NAMES[a]},{TYPE_NAMES[b]},overlap={overlap}]={theta[i]:.9g}")
    else:
        print(f"nonzero_coefficients={sum(abs(x) > 1e-7 for x in theta)}")
    if status == "local-hall":
        print("at least one instance has a local Hall obstruction")
    return 0


if __name__ == "__main__":
    sys.exit(main())
