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
ORDER_CONSTRAINTS: list[tuple[int, int]] = []


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


def root_signature_censuses(data: dict) -> tuple[list[tuple], list[dict]]:
    """Return the full root signatures and role censuses used in (12rb)."""
    signatures = []
    censuses = []
    for t in range(N):
        selected_loads = Counter(
            b for u in data["candidates"][t]
            for b in data["blocks"][u] & data["selected"])
        all_loads = Counter(
            b for u in data["candidates"][t] for b in data["blocks"][u])
        signatures.append((
            data["types"][t], len(data["candidates"][t]),
            sum(x * (x - 1) // 2 for x in selected_loads.values()),
            sum(x * (x - 1) // 2 for x in all_loads.values())))
        censuses.append({
            b: tuple(sum(1 for u in data["candidates"][t]
                         if b in data["blocks"][u]
                         and data["types"][u] == role)
                     for role in range(5))
            for b in data["selected"]})
    return signatures, censuses


def bundle_transition_boundaries(data: dict) -> list[tuple[int, int, Counter]]:
    """Construct exact alpha-plus-bundle boundaries for eligible transitions."""
    signatures, censuses = root_signature_censuses(data)
    answer = []
    for t in range(N):
        own_support = data["blocks"][t] & data["selected"]
        for u in data["candidates"][t]:
            if (data["types"][t] != data["types"][u]
                    or not own_support & data["blocks"][u]):
                continue
            boundary = Counter()
            boundary[("alpha", signatures[t])] += 1
            boundary[("alpha", signatures[u])] -= 1
            for b in data["blocks"][u] & data["selected"]:
                boundary[("bundle", signatures[t],
                          int(b in data["blocks"][t]), censuses[t][b])] += 1
            for b in own_support:
                boundary[("bundle", signatures[u],
                          int(b in data["blocks"][u]), censuses[u][b])] -= 1
            answer.append((t, u, Counter({key: value
                                          for key, value in boundary.items()
                                          if value})))
    return answer


def bundle_boundary_audit(data: dict) -> tuple[int, list[tuple[int, int]]]:
    """Find same-role own transitions with zero whole-bundle boundary."""
    transitions = bundle_transition_boundaries(data)
    return len(transitions), [(t, u) for t, u, boundary in transitions
                              if not boundary]


def bundle_pair_audit(data: dict) -> tuple[int, list[tuple]]:
    """Find exact opposite bundle vectors not explained by route reversal."""
    transitions = bundle_transition_boundaries(data)

    def key(boundary: Counter, sign: int = 1) -> tuple:
        return tuple(sorted(((item, sign * count)
                             for item, count in boundary.items()), key=repr))

    by_boundary = {}
    for t, u, boundary in transitions:
        by_boundary.setdefault(key(boundary), []).append((t, u))
    nonreversal = set()
    for t, u, boundary in transitions:
        for v, w in by_boundary.get(key(boundary, -1), []):
            if (v, w) != (u, t):
                nonreversal.add(tuple(sorted(((t, u), (v, w)))))
    return len(transitions), sorted(nonreversal)


def bundle_triple_audit(data: dict) -> tuple[int, list[tuple]]:
    """Find zero sums of three bundle vectors, allowing repeated atoms."""
    transitions = bundle_transition_boundaries(data)

    def key(boundary: Counter, sign: int = 1) -> tuple:
        return tuple(sorted(((item, sign * count)
                             for item, count in boundary.items() if count),
                            key=repr))

    singles = {}
    for index, (_, _, boundary) in enumerate(transitions):
        singles.setdefault(key(boundary), []).append(index)
    zero_triples = set()
    for left in range(len(transitions)):
        for right in range(left, len(transitions)):
            total = Counter(transitions[left][2])
            total.update(transitions[right][2])
            total = Counter({item: count for item, count in total.items()
                             if count})
            for last in singles.get(key(total, -1), []):
                atoms = tuple(sorted((transitions[index][0],
                                      transitions[index][1])
                                     for index in (left, right, last)))
                zero_triples.add(atoms)
    return len(transitions), sorted(zero_triples)


def bundle_rank_audit(data: dict) -> tuple[
        int, int, list[tuple[int, int]], list[tuple[int, int]]]:
    """Exact rank after quotienting the route-reversal sign relation."""
    from sympy import SparseMatrix

    transitions = {(t, u): boundary
                   for t, u, boundary in bundle_transition_boundaries(data)}
    missing_reverse = sorted((t, u) for t, u in transitions
                             if (u, t) not in transitions)
    indexed_columns = [((t, u), boundary)
                       for (t, u), boundary in transitions.items()
                       if t < u and (u, t) in transitions]
    columns = [boundary for _, boundary in indexed_columns]
    feature_frequency = Counter(feature for boundary in columns
                                for feature, value in boundary.items() if value)
    without_private_feature = [
        edge for edge, boundary in indexed_columns
        if not any(value and feature_frequency[feature] == 1
                   for feature, value in boundary.items())]
    features = sorted({feature for boundary in columns for feature in boundary},
                      key=repr)
    row = {feature: index for index, feature in enumerate(features)}
    entries = {(row[feature], column): value
               for column, boundary in enumerate(columns)
               for feature, value in boundary.items()}
    rank = SparseMatrix(len(features), len(columns), entries).rank()
    return len(columns), rank, missing_reverse, without_private_feature


def flat_signature_audit(data: dict) -> tuple[
        int, int, int, tuple[str, ...], tuple[tuple[int, ...], ...], bool]:
    """Audit the retracted simple signature quotient (12qy).

    A flat pair uses a selected label owned by both roots and makes the two
    same-role roots each other's unique same-role candidate on that label.
    Return the number of nonisolated signatures, quotient edges, parallel
    realizations discarded by the simple quotient, and whether it is a
    forest.  A quotient loop counts as a cycle.
    """
    signatures, _ = root_signature_censuses(data)

    realized_edges = []
    for t in range(N):
        for b in data["blocks"][t] & data["selected"]:
            same_role = [
                u for u in data["candidates"][t]
                if data["types"][u] == data["types"][t]
                and b in data["blocks"][u]]
            if len(same_role) != 1:
                continue
            u = same_role[0]
            reverse = [
                v for v in data["candidates"][u]
                if data["types"][v] == data["types"][u]
                and b in data["blocks"][v]]
            if reverse == [t]:
                realized_edges.append(tuple(sorted((signatures[t], signatures[u]))))

    edge_multiplicity = Counter(realized_edges)
    edges = set(edge_multiplicity)
    vertices = {vertex for edge in edges for vertex in edge}
    adjacency = {vertex: set() for vertex in vertices}
    for left, right in edges:
        adjacency[left].add(right)
        adjacency[right].add(left)
    parent = {vertex: vertex for vertex in vertices}

    def find(vertex: tuple) -> tuple:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    forest = True
    for left, right in edges:
        left_root, right_root = find(left), find(right)
        if left_root == right_root:
            forest = False
        else:
            parent[left_root] = right_root
    parallel = sum(count - 1 for count in edge_multiplicity.values())
    roles = tuple(TYPE_NAMES[role] for role in sorted({edge[0][0] for edge in edges}))
    unseen = set(vertices)
    shapes = []
    while unseen:
        stack = [unseen.pop()]
        component = set(stack)
        while stack:
            vertex = stack.pop()
            for neighbor in adjacency[vertex]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    component.add(neighbor)
                    stack.append(neighbor)
        shapes.append(tuple(sorted(len(adjacency[vertex]) for vertex in component)))
    return (len(vertices), len(edges), parallel, roles,
            tuple(sorted(shapes)), forest)


def refine_features(instances: list[dict], mode: str) -> None:
    """Replace basic vectors by vectors for a finer vertex signature.

    Every refined mode retains candidate count.  ``collisions`` adds
    sum_b binom(load_b, 2), the number of pairs of eligible candidates which
    conflict at a selected U1 label.
    """
    global FEATURES, ORDER_CONSTRAINTS
    ORDER_CONSTRAINTS = []
    if mode in ("fiber-type-total-incidence-linear-farkas",
                "fiber-type-total-incidence-quadratic-farkas",
                "fiber-type-total-incidence-threshold-farkas"):
        quadratic = mode == "fiber-type-total-incidence-quadratic-farkas"
        threshold = mode == "fiber-type-total-incidence-threshold-farkas"
        instance_keys = []
        all_keys = set()
        for data in instances:
            row_signatures = []
            row_censuses = []
            for t in range(N):
                loads = Counter(b for support in data["labels"][t]
                                for b in support)
                collisions = sum(x * (x - 1) // 2 for x in loads.values())
                all_loads = Counter(
                    b for u in data["candidates"][t] for b in data["blocks"][u]
                )
                all_collisions = sum(x * (x - 1) // 2
                                     for x in all_loads.values())
                signature = (data["types"][t],
                             len(data["candidates"][t]),
                             collisions, all_collisions)
                row_signatures.append(signature)
                censuses = {}
                for b in data["selected"]:
                    counts = [0] * 5
                    for u in data["candidates"][t]:
                        if b in data["blocks"][u]:
                            counts[data["types"][u]] += 1
                    censuses[b] = tuple(counts)
                    incidence = int(b in data["blocks"][t])
                    all_keys.add(("mu", "intercept", signature, incidence))
                    for j in range(5):
                        all_keys.add(("mu", "role", signature, incidence, j))
                    if threshold:
                        for j in range(5):
                            for level in range(1, 6):
                                all_keys.add(("mu", "threshold", signature,
                                              incidence, j, level))
                    if quadratic:
                        for j in range(5):
                            for k in range(j, 5):
                                all_keys.add(("mu", "quadratic", signature,
                                              incidence, j, k))
                row_censuses.append(censuses)
                all_keys.add(("alpha", signature))
            instance_keys.append((row_signatures, row_censuses))
        FEATURES = {key: i for i, key in enumerate(sorted(all_keys))}
        for data, (row_signatures, row_censuses) in zip(instances, instance_keys):
            vectors = []
            for t in range(N):
                row_vectors = []
                own_support = data["blocks"][t] & data["selected"]
                for j, u in enumerate(data["candidates"][t]):
                    vector = np.zeros(len(FEATURES))
                    vector[FEATURES[("alpha", row_signatures[t])]] += 1
                    vector[FEATURES[("alpha", row_signatures[u])]] -= 1
                    for b in data["labels"][t][j]:
                        incidence = int(b in data["blocks"][t])
                        vector[FEATURES[("mu", "intercept",
                                         row_signatures[t], incidence)]] += 1
                        for role, count in enumerate(row_censuses[t][b]):
                            vector[FEATURES[("mu", "role", row_signatures[t],
                                             incidence, role)]] += count
                        if threshold:
                            counts = row_censuses[t][b]
                            for role in range(5):
                                for level in range(1, counts[role] + 1):
                                    vector[FEATURES[("mu", "threshold",
                                                     row_signatures[t], incidence,
                                                     role, level)]] += 1
                        if quadratic:
                            counts = row_censuses[t][b]
                            for role in range(5):
                                for other in range(role, 5):
                                    vector[FEATURES[("mu", "quadratic",
                                                     row_signatures[t], incidence,
                                                     role, other)]] += (
                                                         counts[role] * counts[other])
                    for b in own_support:
                        incidence = int(b in data["blocks"][u])
                        vector[FEATURES[("mu", "intercept",
                                         row_signatures[u], incidence)]] -= 1
                        for role, count in enumerate(row_censuses[u][b]):
                            vector[FEATURES[("mu", "role", row_signatures[u],
                                             incidence, role)]] -= count
                        if threshold:
                            counts = row_censuses[u][b]
                            for role in range(5):
                                for level in range(1, counts[role] + 1):
                                    vector[FEATURES[("mu", "threshold",
                                                     row_signatures[u], incidence,
                                                     role, level)]] -= 1
                        if quadratic:
                            counts = row_censuses[u][b]
                            for role in range(5):
                                for other in range(role, 5):
                                    vector[FEATURES[("mu", "quadratic",
                                                     row_signatures[u], incidence,
                                                     role, other)]] -= (
                                                         counts[role] * counts[other])
                    row_vectors.append(vector)
                vectors.append(np.array(row_vectors))
            data["vectors"] = vectors
        return
    if mode in ("fiber-profile-farkas", "fiber-type-profile-farkas",
                "fiber-type-count-farkas", "fiber-type-uncolored-farkas",
                "fiber-type-bare-farkas", "fiber-demand-farkas",
                "fiber-role-farkas", "fiber-type-monotone-farkas",
                "fiber-type-total-monotone-farkas",
                "fiber-type-collision-monotone-farkas",
                "fiber-type-total-incidence-monotone-farkas",
                "fiber-type-total-color-monotone-farkas"):
        instance_keys = []
        all_keys = set()
        for data in instances:
            colors = sorted({b // 8 for b in data["selected"]})
            row_signatures = []
            for t in range(N):
                loads = Counter(b for support in data["labels"][t]
                                for b in support)
                collisions = sum(x * (x - 1) // 2 for x in loads.values())
                all_loads = Counter(
                    b for u in data["candidates"][t] for b in data["blocks"][u]
                )
                all_collisions = sum(x * (x - 1) // 2
                                     for x in all_loads.values())
                root_type = data["types"][t]
                if mode == "fiber-role-farkas" and root_type == 3:
                    root_type = 2
                signature = (root_type, len(data["candidates"][t]), collisions)
                if mode in ("fiber-type-total-monotone-farkas",
                            "fiber-type-collision-monotone-farkas",
                            "fiber-type-total-incidence-monotone-farkas",
                            "fiber-type-total-color-monotone-farkas"):
                    signature += (all_collisions,)
                row_signatures.append(signature)
            mu_keys = []
            for t in range(N):
                occupants = {b: [] for b in data["selected"]}
                for j, u in enumerate(data["candidates"][t]):
                    for b in data["labels"][t][j]:
                        occupant_type = data["types"][u]
                        if mode == "fiber-role-farkas" and occupant_type == 3:
                            occupant_type = 2
                        occupants[b].append(
                            row_signatures[u] if mode == "fiber-profile-farkas"
                            else (int(occupant_type == 0)
                                  if mode == "fiber-demand-farkas"
                                  else occupant_type)
                        )
                row_mu = {}
                for b in data["selected"]:
                    root_signature = (data["types"][t]
                                      if mode == "fiber-type-count-farkas"
                                      else row_signatures[t])
                    key = ("mu", root_signature,
                           tuple(sorted(occupants[b])),
                           int(b in data["blocks"][t]), colors.index(b // 8))
                    if mode in ("fiber-type-uncolored-farkas",
                                "fiber-type-bare-farkas"):
                        key = ("mu", root_signature,
                               tuple(sorted(occupants[b])),
                               int(b in data["blocks"][t]))
                    if mode == "fiber-type-total-incidence-monotone-farkas":
                        key = ("mu", root_signature,
                               tuple(sorted(occupants[b])),
                               int(b in data["blocks"][t]))
                    if mode == "fiber-type-total-color-monotone-farkas":
                        key = ("mu", root_signature,
                               tuple(sorted(occupants[b])),
                               colors.index(b // 8))
                    if mode in ("fiber-type-bare-farkas",
                                "fiber-demand-farkas", "fiber-role-farkas",
                                "fiber-type-monotone-farkas",
                                "fiber-type-total-monotone-farkas",
                                "fiber-type-collision-monotone-farkas"):
                        key = ("mu", root_signature,
                               tuple(sorted(occupants[b])))
                    row_mu[b] = key
                    all_keys.add(key)
                mu_keys.append(row_mu)
                all_keys.add(("alpha", row_signatures[t]))
            instance_keys.append((row_signatures, mu_keys))
        FEATURES = {key: i for i, key in enumerate(sorted(all_keys))}
        if mode in ("fiber-type-monotone-farkas",
                    "fiber-type-total-monotone-farkas",
                    "fiber-type-collision-monotone-farkas",
                    "fiber-type-total-incidence-monotone-farkas",
                    "fiber-type-total-color-monotone-farkas"):
            mu_keys_all = [key for key in FEATURES if key[0] == "mu"]
            for i, left in enumerate(mu_keys_all):
                left_counts = Counter(left[2])
                for right in mu_keys_all[i + 1:]:
                    if left[1] != right[1]:
                        continue
                    if left[3:] != right[3:]:
                        continue
                    right_counts = Counter(right[2])
                    if all(left_counts[j] <= right_counts[j] for j in range(5)):
                        ORDER_CONSTRAINTS.append((FEATURES[left], FEATURES[right]))
                    elif all(right_counts[j] <= left_counts[j] for j in range(5)):
                        ORDER_CONSTRAINTS.append((FEATURES[right], FEATURES[left]))
            if mode == "fiber-type-collision-monotone-farkas":
                # At fixed (role,n,c_pair) and fiber census, charge larger
                # all-color/omitted-color collision by a weakly smaller cap
                # price.  This is the sign suggested by convex concentration.
                for left in mu_keys_all:
                    for right in mu_keys_all:
                        if (left[1][:3] == right[1][:3]
                                and left[2] == right[2]
                                and left[1][3] > right[1][3]):
                            ORDER_CONSTRAINTS.append(
                                (FEATURES[left], FEATURES[right]))
        for data, (row_signatures, mu_keys) in zip(instances, instance_keys):
            vectors = []
            for t in range(N):
                row_vectors = []
                own_support = data["blocks"][t] & data["selected"]
                for j, u in enumerate(data["candidates"][t]):
                    vector = np.zeros(len(FEATURES))
                    vector[FEATURES[("alpha", row_signatures[t])]] += 1
                    vector[FEATURES[("alpha", row_signatures[u])]] -= 1
                    for b in data["labels"][t][j]:
                        vector[FEATURES[mu_keys[t][b]]] += 1
                    for b in own_support:
                        vector[FEATURES[mu_keys[u][b]]] -= 1
                    row_vectors.append(vector)
                vectors.append(np.array(row_vectors))
            data["vectors"] = vectors
        return
    if mode == "invariant-farkas":
        instance_keys = []
        all_keys = set()
        for data in instances:
            colors = sorted({b // 8 for b in data["selected"]})
            row_signatures = []
            mu_keys = []
            for t in range(N):
                loads = Counter(b for support in data["labels"][t]
                                for b in support)
                collisions = sum(x * (x - 1) // 2 for x in loads.values())
                row_signature = (data["types"][t],
                                 len(data["candidates"][t]), collisions)
                row_signatures.append(row_signature)
                row_mu = {}
                for b in data["selected"]:
                    key = ("mu", row_signature, loads[b],
                           int(b in data["blocks"][t]), colors.index(b // 8))
                    row_mu[b] = key
                    all_keys.add(key)
                mu_keys.append(row_mu)
                all_keys.add(("alpha", row_signature))
            instance_keys.append((row_signatures, mu_keys))
        FEATURES = {key: i for i, key in enumerate(sorted(all_keys))}
        for data, (row_signatures, mu_keys) in zip(instances, instance_keys):
            vectors = []
            for t in range(N):
                row_vectors = []
                own_support = data["blocks"][t] & data["selected"]
                for j, u in enumerate(data["candidates"][t]):
                    vector = np.zeros(len(FEATURES))
                    vector[FEATURES[("alpha", row_signatures[t])]] += 1
                    vector[FEATURES[("alpha", row_signatures[u])]] -= 1
                    for b in data["labels"][t][j]:
                        vector[FEATURES[mu_keys[t][b]]] += 1
                    for b in own_support:
                        vector[FEATURES[mu_keys[u][b]]] -= 1
                    row_vectors.append(vector)
                vectors.append(np.array(row_vectors))
            data["vectors"] = vectors
        return
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
        aub = lil_matrix((len(cuts) + len(instances) + len(ORDER_CONSTRAINTS),
                          z_index + 1))
        bub = np.zeros(aub.shape[0])
        for k, (ir, vector) in enumerate(cuts):
            aub[k, :nf] = vector
            aub[k, nf + ir] = -1
        for i in range(len(instances)):
            k = len(cuts) + i
            aub[k, nf + i * N:nf + (i + 1) * N] = 1
            aub[k, z_index] = -1
        offset = len(cuts) + len(instances)
        for k, (lower, upper) in enumerate(ORDER_CONSTRAINTS):
            aub[offset + k, lower] = 1
            aub[offset + k, upper] = -1
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
        rows = len(cuts) + len(instances) + 2 * nf + len(ORDER_CONSTRAINTS)
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
        offset += 2 * nf
        for k, (lower, upper) in enumerate(ORDER_CONSTRAINTS):
            aub[offset + k, lower] = 1
            aub[offset + k, upper] = -1
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


def exact_row_maximum(data: dict, row: int, weights: list[int]) -> int | None:
    """Exact degree-d matching value, using only integer arithmetic.

    A candidate occupies its one or two real selected labels.  A one-label
    candidate's other endpoint is a private dummy, so it creates no additional
    collision and needs no bit in the state.  Thus a dictionary indexed by
    (chosen cardinality, 16-bit real-label mask) is an exact matching oracle.
    """
    selected = sorted(data["selected"])
    bit = {b: 1 << i for i, b in enumerate(selected)}
    demand = int(data["degree"][row])
    states = {(0, 0): 0}
    for support, weight in zip(data["labels"][row], weights):
        occupied = sum(bit[b] for b in support)
        updated = dict(states)
        for (cardinality, mask), value in states.items():
            if cardinality < demand and not mask & occupied:
                key = (cardinality + 1, mask | occupied)
                updated[key] = max(updated.get(key, -(1 << 100)),
                                   value + weight)
        states = updated
    values = [value for (cardinality, _), value in states.items()
              if cardinality == demand]
    return max(values) if values else None


def exact_integral_audit(instances: list[dict], theta: np.ndarray,
                         scale: int) -> tuple[bool, list[int], np.ndarray]:
    """Round a floating separator and verify the result exactly.

    Feature vectors are integral.  After rounding the coefficients, every
    candidate weight and every row/instance optimum below is computed with
    Python integers; the floating MILP oracle is not consulted.
    """
    integral = np.rint(theta * scale).astype(object)
    inverse = {i: key for key, i in FEATURES.items()}
    signs_ok = all(not (isinstance(inverse[i], tuple)
                       and inverse[i] and inverse[i][0] == "mu")
                   or integral[i] >= 0 for i in range(len(integral)))
    orders_ok = all(integral[lower] <= integral[upper]
                    for lower, upper in ORDER_CONSTRAINTS)
    totals = []
    feasible = True
    for data in instances:
        total = 0
        for row in range(N):
            weights = [sum(int(x) * int(y) for x, y in zip(vector, integral))
                       for vector in data["vectors"][row]]
            value = exact_row_maximum(data, row, weights)
            if value is None:
                feasible = False
                break
            total += value
        totals.append(total if feasible else 0)
        if not feasible:
            break
    return feasible and signs_ok and orders_ok and all(x < 0 for x in totals), totals, integral


def main() -> int:
    global FEATURES
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=int, default=1)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument("--max-rounds", type=int, default=100)
    parser.add_argument("--individual", action="store_true",
                        help="fit each locally feasible instance separately")
    parser.add_argument("--sparse", action="store_true",
                        help="minimize coefficient L1 norm at margin -1")
    parser.add_argument("--exact-round-scale", type=int, default=0,
                        help="round the fitted prices at this positive scale "
                             "and audit the separator by exact integer DP")
    parser.add_argument("--audit-flat-signatures", action="store_true",
                        help="regression-audit the retracted terminal (12qy)")
    parser.add_argument("--audit-bundle-boundaries", action="store_true",
                        help="audit exact zero whole-bundle transitions (12rb)")
    parser.add_argument("--audit-bundle-pairs", action="store_true",
                        help="audit non-reversal two-transition cancellations")
    parser.add_argument("--audit-bundle-triples", action="store_true",
                        help="audit exact zero sums of three bundle transitions")
    parser.add_argument("--audit-bundle-rank", action="store_true",
                        help="audit exact rank modulo route reversal")
    parser.add_argument("--require-eligible-hole-pair", action="store_true",
                        help="generate outer witnesses with intersecting "
                             "mutually eligible hole blocks")
    parser.add_argument("--features", choices=("basic", "candidate-count",
                                                "total-load", "collisions",
                                                "load-shape", "load-profile",
                                                "matching-capacity",
                                                "bilinear-collisions",
                                                "collision-differences",
                                                "gradient-collisions",
                                                "free-gradient",
                                                "row-fiber-curl",
                                                "farkas-curl",
                                                "invariant-farkas",
                                                "fiber-profile-farkas",
                                                "fiber-type-profile-farkas",
                                                "fiber-type-count-farkas",
                                                "fiber-type-uncolored-farkas",
                                                "fiber-type-bare-farkas",
                                                "fiber-demand-farkas",
                                                "fiber-role-farkas",
                                                "fiber-type-monotone-farkas",
                                                "fiber-type-total-monotone-farkas",
                                                "fiber-type-collision-monotone-farkas",
                                                "fiber-type-total-incidence-monotone-farkas",
                                                "fiber-type-total-color-monotone-farkas",
                                                "fiber-type-total-incidence-linear-farkas",
                                                "fiber-type-total-incidence-quadratic-farkas",
                                                "fiber-type-total-incidence-threshold-farkas"),
                        default="basic")
    args = parser.parse_args()
    data = []
    all_data = []
    data_labels = []
    hall_labels = []
    for branch in (3, 4):
        for seed_number in range(args.seeds):
            seed = make_outer_seed(
                branch, args.timeout_seconds * 1000, seed_number,
                require_eligible_hole_pair=args.require_eligible_hole_pair)
            for colors in combinations(range(3), 2):
                candidate = instance(branch, seed, colors)
                all_data.append(((branch, seed_number, colors), candidate))
                bad_rows = [row for row in range(N)
                            if oracle(candidate, row, np.zeros(len(FEATURES))) is None]
                if bad_rows:
                    hall_labels.append((branch, seed_number, colors, bad_rows))
                else:
                    data.append(candidate)
                    data_labels.append((branch, seed_number, colors))
    audit_failed = False
    if args.audit_flat_signatures:
        all_forests = True
        for label, candidate in all_data:
            (vertices, edges, parallel, roles, shapes,
             forest) = flat_signature_audit(candidate)
            all_forests &= forest
            branch, seed_number, colors = label
            print(f"flat_signature branch={branch} seed={seed_number} "
                  f"colors={colors} vertices={vertices} edges={edges} "
                  f"parallel_realizations={parallel} roles={roles} "
                  f"component_degree_shapes={shapes} forest={forest}")
        print(f"flat_signature_all_forests={all_forests}")
        audit_failed |= not all_forests
    if args.audit_bundle_boundaries:
        total_tested = 0
        total_zero = 0
        for label, candidate in all_data:
            tested, zero = bundle_boundary_audit(candidate)
            total_tested += tested
            total_zero += len(zero)
            branch, seed_number, colors = label
            print(f"bundle_boundary branch={branch} seed={seed_number} "
                  f"colors={colors} tested={tested} zero={zero}")
        print(f"bundle_boundary_total_tested={total_tested} "
              f"zero_transitions={total_zero}")
        audit_failed |= total_zero > 0
    if args.audit_bundle_pairs:
        total_tested = 0
        total_pairs = 0
        for label, candidate in all_data:
            tested, pairs = bundle_pair_audit(candidate)
            total_tested += tested
            total_pairs += len(pairs)
            branch, seed_number, colors = label
            print(f"bundle_pairs branch={branch} seed={seed_number} "
                  f"colors={colors} tested={tested} nonreversal={pairs}")
        print(f"bundle_pairs_total_tested={total_tested} "
              f"nonreversal_pairs={total_pairs}")
        audit_failed |= total_pairs > 0
    if args.audit_bundle_triples:
        total_tested = 0
        total_triples = 0
        for label, candidate in all_data:
            tested, triples = bundle_triple_audit(candidate)
            total_tested += tested
            total_triples += len(triples)
            branch, seed_number, colors = label
            print(f"bundle_triples branch={branch} seed={seed_number} "
                  f"colors={colors} tested={tested} zero={triples}")
        print(f"bundle_triples_total_tested={total_tested} "
              f"zero_triples={total_triples}")
        audit_failed |= total_triples > 0
    if args.audit_bundle_rank:
        total_columns = 0
        total_rank = 0
        total_missing = 0
        total_nonprivate = 0
        for label, candidate in all_data:
            columns, rank, missing, nonprivate = bundle_rank_audit(candidate)
            total_columns += columns
            total_rank += rank
            total_missing += len(missing)
            total_nonprivate += len(nonprivate)
            branch, seed_number, colors = label
            print(f"bundle_rank branch={branch} seed={seed_number} "
                  f"colors={colors} columns={columns} rank={rank} "
                  f"missing_reverse={missing} nonprivate={nonprivate}")
        print(f"bundle_rank_total_columns={total_columns} "
              f"total_rank={total_rank} missing_reverse={total_missing} "
              f"nonprivate={total_nonprivate}")
        audit_failed |= (total_rank != total_columns or total_missing > 0
                         or total_nonprivate > 0)
    for branch, seed_number, colors, bad_rows in hall_labels:
        print(f"local_hall branch={branch} seed={seed_number} "
              f"colors={colors} rows={bad_rows}")
    if (args.audit_flat_signatures or args.audit_bundle_boundaries
            or args.audit_bundle_pairs or args.audit_bundle_triples
            or args.audit_bundle_rank):
        return 1 if audit_failed else 0
    if not data:
        print(f"instances=0 local_hall_instances={len(hall_labels)}")
        return 0
    if args.individual:
        for label, candidate in zip(data_labels, data):
            if args.features != "basic":
                FEATURES = feature_index()
                refine_features([candidate], args.features)
            fitter = fit_sparse if args.sparse else fit
            status, objective, theta, rounds = fitter([candidate], args.max_rounds)
            branch, seed_number, colors = label
            print(f"individual branch={branch} seed={seed_number} colors={colors} "
                  f"features={len(FEATURES)} status={status} "
                  f"objective={objective:.9g} rounds={rounds}")
            if args.exact_round_scale:
                if args.exact_round_scale < 1:
                    parser.error("--exact-round-scale must be positive")
                exact, totals, integral = exact_integral_audit(
                    [candidate], theta, args.exact_round_scale)
                print(f"individual_exact_integral_audit="
                      f"{'pass' if exact else 'fail'} "
                      f"scale={args.exact_round_scale} totals={totals} "
                      f"max_abs_coefficient="
                      f"{max(abs(int(x)) for x in integral)}")
                if status == "separates" and not exact:
                    return 1
        return 0
    if args.features != "basic":
        refine_features(data, args.features)
        print(f"feature_mode={args.features} feature_count={len(FEATURES)}")
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
    if args.exact_round_scale:
        if args.exact_round_scale < 1:
            parser.error("--exact-round-scale must be positive")
        exact, totals, integral = exact_integral_audit(
            data, theta, args.exact_round_scale)
        print(f"exact_integral_audit={'pass' if exact else 'fail'} "
              f"scale={args.exact_round_scale} totals={totals} "
              f"max_abs_coefficient={max(abs(int(x)) for x in integral)}")
        if not exact:
            return 1
    if status == "local-hall":
        print("at least one instance has a local Hall obstruction")
    return 0


if __name__ == "__main__":
    sys.exit(main())
