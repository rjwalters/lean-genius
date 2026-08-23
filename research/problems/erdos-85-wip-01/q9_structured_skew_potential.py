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
import os
import sys
from collections import Counter
from fractions import Fraction
from itertools import combinations

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import lil_matrix, vstack

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
        int, int, list[tuple[int, int]], list[tuple[int, int]],
        list[tuple[int, int]], list[tuple[int, int]]]:
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
    without_private_bundle = [
        edge for edge, boundary in indexed_columns
        if not any(value and feature[0] == "bundle"
                   and feature_frequency[feature] == 1
                   for feature, value in boundary.items())]
    without_private_external = [
        edge for edge, boundary in indexed_columns
        if not any(value and feature[0] == "bundle" and feature[2] == 0
                   and feature_frequency[feature] == 1
                   for feature, value in boundary.items())]
    features = sorted({feature for boundary in columns for feature in boundary},
                      key=repr)
    row = {feature: index for index, feature in enumerate(features)}
    entries = {(row[feature], column): value
               for column, boundary in enumerate(columns)
               for feature, value in boundary.items()}
    rank = SparseMatrix(len(features), len(columns), entries).rank()
    return (len(columns), rank, missing_reverse, without_private_feature,
            without_private_bundle, without_private_external)


def maximum_label_packing(supports: list[set[int]], selected: set[int],
                          initial_mask: int = 0) -> int:
    """Maximum cardinality of pairwise label-disjoint supports, exactly."""
    bit = {label: 1 << index for index, label in enumerate(sorted(selected))}
    states = {initial_mask: 0}
    for support in supports:
        occupied = sum(bit[label] for label in support)
        updated = dict(states)
        for mask, cardinality in states.items():
            if not mask & occupied:
                new_mask = mask | occupied
                updated[new_mask] = max(updated.get(new_mask, -1),
                                        cardinality + 1)
        states = updated
    return max(states.values())


def external_deletion_loss(data: dict, t: int, u: int) -> int:
    """Exact external matching-rank loss caused by the other labels of u."""
    own_support = data["blocks"][t] & data["selected"]
    deleted = (data["blocks"][u] & data["selected"]) - own_support
    external = [data["blocks"][v] & data["selected"]
                for v in data["candidates"][t]
                if not (data["blocks"][v] & data["selected"]) & own_support]
    retained = [support for support in external if not support & deleted]
    return (maximum_label_packing(external, data["selected"])
            - maximum_label_packing(retained, data["selected"]))


def forced_candidate_feasible(data: dict, t: int, u: int) -> bool:
    """Whether some required-cardinality local matching contains candidate u."""
    selected = data["selected"]
    bit = {label: 1 << index for index, label in enumerate(sorted(selected))}
    forced_support = data["blocks"][u] & selected
    forced_mask = sum(bit[label] for label in forced_support)
    remaining = [data["blocks"][v] & selected
                 for v in data["candidates"][t] if v != u
                 and not (data["blocks"][v] & selected) & forced_support]
    return (1 + maximum_label_packing(remaining, selected, forced_mask)
            >= int(data["degree"][t]))


def bundle_deletion_audit(data: dict) -> tuple[
        Counter, list[tuple], tuple[tuple[int, ...], ...]]:
    """Classify bidirectional deletion loss after bundle route pairing."""
    transitions = {(t, u) for t, u, _ in bundle_transition_boundaries(data)}
    losses = Counter()
    zero_pairs = []
    for t, u in transitions:
        if t >= u:
            continue
        forward = external_deletion_loss(data, t, u)
        reverse = external_deletion_loss(data, u, t)
        losses[(forward, reverse)] += 1
        if forward + reverse == 0:
            zero_pairs.append((t, u, forced_candidate_feasible(data, t, u),
                               forced_candidate_feasible(data, u, t)))
    adjacency = {}
    for t, u, _, _ in zero_pairs:
        adjacency.setdefault(t, set()).add(u)
        adjacency.setdefault(u, set()).add(t)
    unseen = set(adjacency)
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
        shapes.append(tuple(sorted(len(adjacency[vertex])
                                   for vertex in component)))
    return losses, sorted(zero_pairs), tuple(sorted(shapes))


def zero_loss_restricted_hall_audit(data: dict) -> tuple[int, list[tuple]]:
    """Keep external candidates and zero-loss own transitions, then test Hall."""
    _, zero_pairs, _ = bundle_deletion_audit(data)
    zero = {(t, u) for t, u, _, _ in zero_pairs}
    zero |= {(u, t) for t, u, _, _ in zero_pairs}
    bad_rows = []
    for t in range(N):
        own_support = data["blocks"][t] & data["selected"]
        supports = [data["blocks"][u] & data["selected"]
                    for u in data["candidates"][t]
                    if not own_support & data["blocks"][u] or (t, u) in zero]
        capacity = maximum_label_packing(supports, data["selected"])
        demand = int(data["degree"][t])
        if capacity < demand:
            bad_rows.append((t, capacity, demand))
    return len(zero) // 2, bad_rows


def full_bundle_primal_system(data: dict) -> tuple:
    """Build normalized row, capacity, and bundle-boundary constraints."""
    signatures, censuses = root_signature_censuses(data)
    variables = []
    for t in range(N):
        own_support = data["blocks"][t] & data["selected"]
        for u in data["candidates"][t]:
            boundary = Counter()
            boundary[("alpha", signatures[t])] += 1
            boundary[("alpha", signatures[u])] -= 1
            for b in data["blocks"][u] & data["selected"]:
                boundary[("bundle", signatures[t],
                          int(b in data["blocks"][t]), censuses[t][b])] += 1
            for b in own_support:
                boundary[("bundle", signatures[u],
                          int(b in data["blocks"][u]), censuses[u][b])] -= 1
            variables.append((t, data["blocks"][u] & data["selected"],
                              {key: value for key, value in boundary.items()
                               if value}))
    features = sorted({key for _, _, boundary in variables for key in boundary},
                      key=repr)
    feature_index = {key: index for index, key in enumerate(features)}
    equalities = lil_matrix((N + len(features), len(variables)))
    equality_rhs = np.zeros(N + len(features))
    for column, (t, _, boundary) in enumerate(variables):
        equalities[t, column] = 1
        for key, value in boundary.items():
            equalities[N + feature_index[key], column] = value
    for t in range(N):
        equality_rhs[t] = int(data["degree"][t])
    capacity_rows = [(t, b) for t in range(N) for b in data["selected"]]
    capacities = lil_matrix((len(capacity_rows), len(variables)))
    for row, (t, b) in enumerate(capacity_rows):
        for column, (source, support, _) in enumerate(variables):
            if source == t and b in support:
                capacities[row, column] = 1
    equality_names = ([('row', t) for t in range(N)]
                      + [('feature', key) for key in features])
    capacity_names = [('capacity', t, b) for t, b in capacity_rows]
    return (equalities.tocsr(), equality_rhs, capacities.tocsr(),
            np.ones(len(capacity_rows)), equality_names, capacity_names,
            len(variables))


def full_bundle_primal_feasible(data: dict) -> tuple[bool, str]:
    """Test normalized row matchings with exact bundle-boundary equality."""
    (equalities, equality_rhs, capacities, capacity_rhs, _, _,
     variable_count) = full_bundle_primal_system(data)
    result = linprog(
        np.zeros(variable_count), A_ub=capacities,
        b_ub=capacity_rhs, A_eq=equalities,
        b_eq=equality_rhs, bounds=(0, 1), method="highs")
    return result.success, result.message


def full_bundle_primal_ablation(data: dict) -> dict[str, bool]:
    """Test which feature layers first make the normalized primal infeasible."""
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     _, variable_count) = full_bundle_primal_system(data)
    feature_predicates = {
        'rows': lambda feature: False,
        'alpha': lambda feature: feature[0] == 'alpha',
        'external': lambda feature: feature[0] == 'bundle' and feature[2] == 0,
        'internal': lambda feature: feature[0] == 'bundle' and feature[2] == 1,
        'bundles': lambda feature: feature[0] == 'bundle',
        'alpha_external': lambda feature: (feature[0] == 'alpha'
                                            or feature[0] == 'bundle'
                                            and feature[2] == 0),
        'alpha_internal': lambda feature: (feature[0] == 'alpha'
                                            or feature[0] == 'bundle'
                                            and feature[2] == 1),
        'full': lambda feature: True,
    }
    answer = {}
    for name, predicate in feature_predicates.items():
        selected_rows = list(range(N)) + [
            row for row in range(N, equalities.shape[0])
            if predicate(equality_names[row][1])]
        result = linprog(
            np.zeros(variable_count), A_ub=capacities,
            b_ub=capacity_rhs, A_eq=equalities[selected_rows],
            b_eq=equality_rhs[selected_rows], bounds=(0, 1), method='highs')
        answer[name] = result.success
    return answer


def external_bundle_coarsening_audit(data: dict) -> dict[str, bool]:
    """Test which coordinates of the external joint state are indispensable."""
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     _, variable_count) = full_bundle_primal_system(data)
    external_rows = [row for row in range(N, equalities.shape[0])
                     if equality_names[row][1][0] == 'bundle'
                     and equality_names[row][1][2] == 0]

    def state(row):
        feature = equality_names[row][1]
        return feature[1], feature[3]

    projections = {
        'full': lambda signature, census: (signature, census),
        'signature': lambda signature, census: signature,
        'census': lambda signature, census: census,
        'type_census': lambda signature, census: (signature[0], census),
        'count_census': lambda signature, census: (signature[1], census),
        'selected_collision_census':
            lambda signature, census: (signature[2], census),
        'all_collision_census':
            lambda signature, census: (signature[3], census),
    }
    for omitted in range(4):
        projections[f'drop_signature_{omitted}'] = (
            lambda signature, census, omitted=omitted:
            (signature[:omitted] + signature[omitted + 1:], census))
    for omitted in range(5):
        projections[f'drop_census_{omitted}'] = (
            lambda signature, census, omitted=omitted:
            (signature, census[:omitted] + census[omitted + 1:]))
        projections[f'selected_collision_drop_census_{omitted}'] = (
            lambda signature, census, omitted=omitted:
            (signature[2], census[:omitted] + census[omitted + 1:]))
        projections[f'all_collision_drop_census_{omitted}'] = (
            lambda signature, census, omitted=omitted:
            (signature[3], census[:omitted] + census[omitted + 1:]))
        projections[f'collision_pair_drop_census_{omitted}'] = (
            lambda signature, census, omitted=omitted:
            ((signature[2], signature[3]),
             census[:omitted] + census[omitted + 1:]))
    for role in range(5):
        projections[f'selected_collision_census_{role}'] = (
            lambda signature, census, role=role: (signature[2], census[role]))
        projections[f'all_collision_census_{role}'] = (
            lambda signature, census, role=role: (signature[3], census[role]))
        projections[f'collision_pair_census_{role}'] = (
            lambda signature, census, role=role:
            ((signature[2], signature[3]), census[role]))
    projections['selected_collision_census_total'] = (
        lambda signature, census: (signature[2], sum(census)))
    projections['all_collision_census_total'] = (
        lambda signature, census: (signature[3], sum(census)))
    for size in range(1, 5):
        for coordinates in combinations(range(4), size):
            label = ''.join(map(str, coordinates))
            projections[f'signature_subset_{label}'] = (
                lambda signature, census, coordinates=coordinates:
                (tuple(signature[index] for index in coordinates), census))

    answer = {}
    for name, projection in projections.items():
        groups = {}
        for row in external_rows:
            signature, census = state(row)
            groups.setdefault(projection(signature, census), []).append(row)
        grouped_rows = [equalities[rows].sum(axis=0) for rows in groups.values()]
        projected = vstack([equalities[:N], *grouped_rows], format='csr')
        result = linprog(
            np.zeros(variable_count), A_ub=capacities,
            b_ub=capacity_rhs, A_eq=projected,
            b_eq=np.r_[equality_rhs[:N], np.zeros(len(grouped_rows))],
            bounds=(0, 1), method='highs')
        answer[name] = result.success
    return answer


def collision_census_primal_system(data: dict) -> tuple:
    """Project external bundle states to the seven coordinates in (12rz)."""
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     capacity_names, variable_count) = full_bundle_primal_system(data)
    groups = {}
    for row in range(N, equalities.shape[0]):
        feature = equality_names[row][1]
        if feature[0] != 'bundle' or feature[2] != 0:
            continue
        signature, census = feature[1], feature[3]
        key = (signature[2], signature[3], *census)
        groups.setdefault(key, []).append(row)
    keys = sorted(groups, key=repr)
    grouped_rows = [equalities[groups[key]].sum(axis=0) for key in keys]
    projected = vstack([equalities[:N], *grouped_rows], format='csr')
    names = ([('row', t) for t in range(N)]
             + [('external_state', key) for key in keys])
    return (projected, np.r_[equality_rhs[:N], np.zeros(len(keys))],
            capacities, capacity_rhs, names, capacity_names, variable_count)


def double_label_flag_primal_system(data: dict, mode: str = "full") -> tuple:
    """Conserve occurrence flags (transported b, collision c, role pair)."""
    (base_equalities, equality_rhs, capacities, capacity_rhs, _,
     capacity_names, variable_count) = full_bundle_primal_system(data)
    profiles = []
    for t in range(N):
        profile = Counter()
        for c in data["selected"]:
            counts = [sum(1 for u in data["candidates"][t]
                          if c in data["blocks"][u]
                          and data["types"][u] == role)
                      for role in range(5)]
            for left in range(5):
                profile[(c, left, left)] = counts[left] * (counts[left] - 1) // 2
                for right in range(left + 1, 5):
                    profile[(c, left, right)] = counts[left] * counts[right]
        profiles.append(+profile)
    variables = []
    feature_keys = set()

    def project(b: int, c: int, left: int, right: int) -> tuple:
        if mode == "full":
            return b, c, left, right
        if mode == "unordered":
            return min(b, c), max(b, c), left, right
        if mode == "transported":
            return b, left, right
        if mode == "witness":
            return c, left, right
        if mode == "equality":
            return int(b == c), left, right
        if mode == "roles":
            return left, right
        raise ValueError(f"unknown double-label projection {mode}")

    for t in range(N):
        own_support = data["blocks"][t] & data["selected"]
        for u in data["candidates"][t]:
            boundary = Counter()
            for b in (data["blocks"][u] & data["selected"]) - own_support:
                for (c, left, right), count in profiles[t].items():
                    boundary[project(b, c, left, right)] += count
            for b in own_support - data["blocks"][u]:
                for (c, left, right), count in profiles[u].items():
                    boundary[project(b, c, left, right)] -= count
            variables.append(boundary)
            feature_keys.update(boundary)
    keys = sorted(feature_keys)
    key_index = {key: row for row, key in enumerate(keys)}
    flag_rows = lil_matrix((len(keys), variable_count))
    for column, boundary in enumerate(variables):
        for key, value in boundary.items():
            flag_rows[key_index[key], column] = value
    equalities = vstack([base_equalities[:N], flag_rows], format='csr')
    names = ([('row', t) for t in range(N)]
             + [('double_label_flag', key) for key in keys])
    return (equalities, np.r_[equality_rhs[:N], np.zeros(len(keys))],
            capacities, capacity_rhs, names, capacity_names, variable_count)


def double_label_flag_primal_audit(data: dict, mode: str = "full") -> tuple:
    """Test row demands, capacities, and double-labelled flag conservation."""
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     _, variable_count) = double_label_flag_primal_system(data, mode)
    result = linprog(
        np.zeros(variable_count), A_ub=capacities, b_ub=capacity_rhs,
        A_eq=equalities, b_eq=equality_rhs, bounds=(0, 1), method='highs')
    return result.success, equalities.shape[0] - N, result.message


def half_atom_primal_system(data: dict) -> tuple:
    """Conserve the abstract (root, externally transported label) atoms."""
    (base_equalities, equality_rhs, capacities, capacity_rhs, _,
     capacity_names, variable_count) = full_bundle_primal_system(data)
    variables = []
    keys = set()
    for t in range(N):
        own_support = data["blocks"][t] & data["selected"]
        for u in data["candidates"][t]:
            boundary = Counter()
            for b in (data["blocks"][u] & data["selected"]) - own_support:
                boundary[(t, b)] += 1
            for b in own_support - data["blocks"][u]:
                boundary[(u, b)] -= 1
            variables.append(boundary)
            keys.update(boundary)
    keys = sorted(keys)
    key_index = {key: row for row, key in enumerate(keys)}
    atom_rows = lil_matrix((len(keys), variable_count))
    for column, boundary in enumerate(variables):
        for key, value in boundary.items():
            atom_rows[key_index[key], column] = value
    equalities = vstack([base_equalities[:N], atom_rows], format='csr')
    names = ([('row', t) for t in range(N)]
             + [('half_atom', key) for key in keys])
    return (equalities, np.r_[equality_rhs[:N], np.zeros(len(keys))],
            capacities, capacity_rhs, names, capacity_names, variable_count)


def half_atom_primal_audit(data: dict) -> tuple:
    system = half_atom_primal_system(data)
    equalities, equality_rhs, capacities, capacity_rhs, _, _, variable_count = system
    result = linprog(
        np.zeros(variable_count), A_ub=capacities, b_ub=capacity_rhs,
        A_eq=equalities, b_eq=equality_rhs, bounds=(0, 1), method='highs')
    return result.success, equalities.shape[0] - N, result.message


def double_label_flag_private_audit(data: dict) -> tuple:
    """Check private unordered-flag rows after quotienting route reversal."""
    from scipy.linalg import qr, solve_triangular

    equalities, _, _, _, _, _, _ = double_label_flag_primal_system(
        data, "unordered")
    edges = [(t, u) for t in range(N) for u in data["candidates"][t]]
    edge_set = set(edges)
    missing_reverse = sorted((t, u) for t, u in edges if (u, t) not in edge_set)
    selected = [(column, edge) for column, edge in enumerate(edges)
                if edge[0] < edge[1] and (edge[1], edge[0]) in edge_set]
    matrix = equalities[N:, [column for column, _ in selected]].tocsr()
    frequency = np.diff(matrix.indptr)
    by_column = matrix.tocsc()
    without_private = []
    signatures = Counter()
    for local_column, (_, edge) in enumerate(selected):
        rows = by_column.indices[
            by_column.indptr[local_column]:by_column.indptr[local_column + 1]]
        values = by_column.data[
            by_column.indptr[local_column]:by_column.indptr[local_column + 1]]
        signatures[tuple(zip(rows, values))] += 1
        if not any(frequency[row] == 1 for row in rows):
            without_private.append(edge)
    dense = matrix.toarray()
    _, triangular, pivots = qr(dense, mode='economic', pivoting=True)
    diagonal = np.abs(np.diag(triangular))
    tolerance = (max(dense.shape) * np.finfo(float).eps
                 * (diagonal[0] if len(diagonal) else 0.0))
    rank = int(np.sum(diagonal > tolerance))
    free_count = dense.shape[1] - rank
    if free_count:
        basic = -solve_triangular(triangular[:rank, :rank],
                                  triangular[:rank, rank:], lower=False)
        fundamental_supports = []
        small_relations = []
        for free_column in range(free_count):
            vector = np.zeros(dense.shape[1])
            vector[pivots[:rank]] = basic[:, free_column]
            vector[pivots[rank + free_column]] = 1.0
            support = np.flatnonzero(np.abs(vector) > 1e-8)
            fundamental_supports.append(len(support))
            if len(support) <= 5:
                scale = min(abs(vector[index]) for index in support)
                small_relations.append(tuple(
                    (selected[index][1], round(float(vector[index] / scale), 8))
                    for index in support))
        fundamental_supports.sort()
    else:
        fundamental_supports = []
        small_relations = []
    duplicate_groups = sorted((count for count in signatures.values() if count > 1),
                              reverse=True)
    duplicate_excess = sum(count - 1 for count in duplicate_groups)
    edge_column = {edge: column for column, (_, edge) in enumerate(selected)}
    support_roots = {}
    for root in range(N):
        support = frozenset(data["blocks"][root] & data["selected"])
        support_roots.setdefault(support, []).append(root)
    triangle_vectors = []
    for pair, unions in support_roots.items():
        if len(pair) != 2:
            continue
        left_label, right_label = sorted(pair)
        for left in support_roots.get(frozenset((left_label,)), []):
            for right in support_roots.get(frozenset((right_label,)), []):
                for union in unions:
                    routes = ((left, right, 1), (left, union, -1),
                              (right, union, 1))
                    vector = np.zeros(len(selected))
                    valid = True
                    for source, target, coefficient in routes:
                        edge = tuple(sorted((source, target)))
                        if edge not in edge_column:
                            valid = False
                            break
                        orientation = 1 if source < target else -1
                        vector[edge_column[edge]] += coefficient * orientation
                    if valid:
                        triangle_vectors.append(vector)
    triangle_rank = (int(np.linalg.matrix_rank(np.array(triangle_vectors)))
                     if triangle_vectors else 0)
    atom_keys = set()
    atom_columns = []
    for _, (left, right) in selected:
        left_support = data["blocks"][left] & data["selected"]
        right_support = data["blocks"][right] & data["selected"]
        column = Counter()
        for label in right_support - left_support:
            column[(left, label)] += 1
        for label in left_support - right_support:
            column[(right, label)] -= 1
        atom_columns.append(column)
        atom_keys.update(column)
    atom_index = {key: row for row, key in enumerate(sorted(atom_keys))}
    atom_matrix = np.zeros((len(atom_keys), len(selected)))
    for column, values in enumerate(atom_columns):
        for key, value in values.items():
            atom_matrix[atom_index[key], column] = value
    atom_rank = int(np.linalg.matrix_rank(atom_matrix))
    return (len(selected), rank, missing_reverse, without_private,
            duplicate_excess, duplicate_groups, fundamental_supports,
            small_relations, len(triangle_vectors), triangle_rank,
            atom_rank)


def collision_census_infeasible_core(data: dict) -> tuple:
    """Greedily delete seven-state equations to an irreducible LP core."""
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     _, variable_count) = collision_census_primal_system(data)
    retained = list(range(N, equalities.shape[0]))
    for row in list(retained):
        trial_states = [candidate for candidate in retained if candidate != row]
        selected = list(range(N)) + trial_states
        result = linprog(
            np.zeros(variable_count), A_ub=capacities,
            b_ub=capacity_rhs, A_eq=equalities[selected],
            b_eq=equality_rhs[selected], bounds=(0, 1), method='highs')
        if not result.success:
            retained.remove(row)
    keys = tuple(equality_names[row][1] for row in retained)
    return equalities.shape[0] - N, len(keys), keys


def sparse_bundle_dual_system(system: tuple) -> tuple[bool, float, list[tuple], bool]:
    """Find an L1-small Farkas certificate for a supplied primal system."""
    from scipy.sparse import hstack

    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     capacity_names, variable_count) = system
    equality_count = equalities.shape[0]
    capacity_count = capacities.shape[0]
    # y is free (split as y+ - y-), z>=0, with
    # E^T y + C^T z >= 0 and b^T y + 1^T z = -1.
    inequalities = hstack([-equalities.T, equalities.T, -capacities.T],
                          format='csr')
    certificate_rhs = lil_matrix((1, 2 * equality_count + capacity_count))
    certificate_rhs[0, :equality_count] = equality_rhs
    certificate_rhs[0, equality_count:2 * equality_count] = -equality_rhs
    certificate_rhs[0, 2 * equality_count:] = capacity_rhs
    result = linprog(
        np.ones(2 * equality_count + capacity_count),
        A_ub=inequalities, b_ub=np.zeros(variable_count),
        A_eq=certificate_rhs.tocsr(), b_eq=[-1], bounds=(0, None),
        method='highs')
    if not result.success:
        return False, float('nan'), [], False
    y = result.x[:equality_count] - result.x[equality_count:2 * equality_count]
    z = result.x[2 * equality_count:]
    nonzero = ([(equality_names[index], value) for index, value in enumerate(y)
                if abs(value) > 1e-8]
               + [(capacity_names[index], value) for index, value in enumerate(z)
                  if value > 1e-8])
    rounded_y = np.rint(y).astype(int)
    rounded_z = np.rint(z).astype(int)
    column_values = equalities.T @ rounded_y + capacities.T @ rounded_z
    scalar = int(equality_rhs @ rounded_y + capacity_rhs @ rounded_z)
    exact = bool(np.all(column_values >= 0) and scalar == -1
                 and np.max(np.abs(y - rounded_y), initial=0) < 1e-8
                 and np.max(np.abs(z - rounded_z), initial=0) < 1e-8)
    return True, float(result.fun), nonzero, exact


def rational_farkas_audit(system: tuple, nonzero: list[tuple],
                          max_denominator: int = 10000000) -> tuple:
    """Rationalize and exactly verify a floating Farkas certificate."""
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     capacity_names, variable_count) = system
    values = {name: Fraction(float(value)).limit_denominator(max_denominator)
              for name, value in nonzero}
    y = [values.get(name, Fraction(0)) for name in equality_names]
    z = [values.get(name, Fraction(0)) for name in capacity_names]
    if any(value < 0 for value in z):
        return False, Fraction(0), 0, Fraction(0)
    equality_columns = equalities.tocsc()
    capacity_columns = capacities.tocsc()
    minimum_slack = None
    for column in range(variable_count):
        slack = Fraction(0)
        for offset in range(equality_columns.indptr[column],
                            equality_columns.indptr[column + 1]):
            row = equality_columns.indices[offset]
            slack += Fraction(int(equality_columns.data[offset])) * y[row]
        for offset in range(capacity_columns.indptr[column],
                            capacity_columns.indptr[column + 1]):
            row = capacity_columns.indices[offset]
            slack += Fraction(int(capacity_columns.data[offset])) * z[row]
        minimum_slack = slack if minimum_slack is None else min(minimum_slack,
                                                                slack)
    scalar = (sum(Fraction(int(value)) * price
                  for value, price in zip(equality_rhs, y))
              + sum(Fraction(int(value)) * price
                    for value, price in zip(capacity_rhs, z)))
    denominator = max((value.denominator for value in (*y, *z)), default=1)
    return minimum_slack is not None and minimum_slack >= 0 and scalar < 0, \
        scalar, denominator, minimum_slack


def sparse_full_bundle_dual(data: dict) -> tuple[bool, float, list[tuple], bool]:
    """Find an L1-small full-ledger Farkas certificate."""
    return sparse_bundle_dual_system(full_bundle_primal_system(data))


def sparse_collision_census_dual(
        data: dict) -> tuple[bool, float, list[tuple], bool]:
    """Find an L1-small dual using only the seven-coordinate state."""
    return sparse_bundle_dual_system(collision_census_primal_system(data))


def sparse_half_atom_dual(data: dict) -> tuple:
    """Find and exactly rational-audit a half-atom Farkas certificate."""
    system = half_atom_primal_system(data)
    success, norm, nonzero, integer = sparse_bundle_dual_system(system)
    rational = (rational_farkas_audit(system, nonzero) if success
                else (False, Fraction(0), 0, Fraction(0)))
    return success, norm, nonzero, integer, rational


def projected_half_atom_dual(data: dict, mode: str) -> tuple:
    """Constrain half-atom prices to a root/label invariant projection."""
    from scipy.sparse import hstack

    system = half_atom_primal_system(data)
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     capacity_names, variable_count) = system
    signatures, censuses = root_signature_censuses(data)
    type_profiles = {}
    signature_profiles = {}
    bare_profiles = {}
    typed_profiles = {}
    load_profiles = {}
    load_moments = {}
    moment_profiles = {}
    for b in data["selected"]:
        loads = [sum(censuses[t][b]) for t in range(N)]
        load_sum = sum(loads)
        fiber_degree_sum = sum(len(data["candidates"][u]) for u in range(N)
                               if b in data["blocks"][u])
        if load_sum != fiber_degree_sum:
            raise RuntimeError("label load Fubini identity failed")
        load_moments[b] = (load_sum, sum(load * load for load in loads))
        load_profiles[b] = tuple(sorted(Counter(
            loads).items()))
        moment_profiles[b] = tuple(
            sum(censuses[t][b][role] ** power for t in range(N))
            for role in range(5) for power in (1, 2))
        bare_profiles[b] = tuple(sorted(Counter(
            censuses[t][b] for t in range(N)).items()))
        typed_profiles[b] = tuple(sorted(Counter(
            (data["types"][t], censuses[t][b]) for t in range(N)).items()))
        type_profiles[b] = tuple(sorted(Counter(
            (data["types"][t], censuses[t][b],
             int(b in data["blocks"][t])) for t in range(N)).items()))
        signature_profiles[b] = tuple(sorted(Counter(
            (signatures[t], censuses[t][b],
             int(b in data["blocks"][t])) for t in range(N)).items()))
    load_total = sum(load_moments[b][0] for b in data["selected"])

    def root_key(t: int):
        if mode.startswith("root-"):
            return t
        if mode.startswith("type-"):
            return data["types"][t]
        if mode.startswith("signature-") or mode.startswith("census-"):
            return signatures[t]
        raise ValueError(f"unknown half-atom projection {mode}")

    def label_key(t: int, b: int):
        suffix = mode.split("-", 1)[1]
        if suffix == "color":
            result = b // 8
        elif suffix == "label":
            result = b
        elif suffix == "typeprofile":
            result = type_profiles[b]
        elif suffix == "signatureprofile":
            result = signature_profiles[b]
        elif suffix == "bareprofile":
            result = bare_profiles[b]
        elif suffix == "typedprofile":
            result = typed_profiles[b]
        elif suffix == "loadprofile":
            result = load_profiles[b]
        elif suffix == "loadmoment":
            result = load_moments[b]
        elif suffix == "loadsum":
            result = load_moments[b][0]
        elif suffix == "loadsquare":
            result = load_moments[b][1]
        elif suffix == "loadparity":
            result = load_moments[b][0] % 2
        elif suffix == "loadsign":
            centered = len(data["selected"]) * load_moments[b][0] - load_total
            result = (centered > 0) - (centered < 0)
        elif suffix == "loadsignparity":
            centered = len(data["selected"]) * load_moments[b][0] - load_total
            result = ((centered > 0) - (centered < 0),
                      load_moments[b][0] % 2)
        elif suffix == "momentprofile":
            result = moment_profiles[b]
        else:
            raise ValueError(f"unknown half-atom label projection {mode}")
        if mode.startswith("census-"):
            return result, censuses[t][b]
        return result

    equality_groups = []
    for name in equality_names:
        if name[0] == "row":
            equality_groups.append(("row", root_key(name[1])))
        else:
            t, b = name[1]
            equality_groups.append(("atom", root_key(t), label_key(t, b)))
    capacity_groups = [
        ("capacity", root_key(t), label_key(t, b))
        for _, t, b in capacity_names]
    equality_keys = sorted(set(equality_groups), key=repr)
    capacity_keys = sorted(set(capacity_groups), key=repr)
    equality_index = {key: index for index, key in enumerate(equality_keys)}
    capacity_index = {key: index for index, key in enumerate(capacity_keys)}
    equality_projection = lil_matrix((len(equality_names), len(equality_keys)))
    capacity_projection = lil_matrix((len(capacity_names), len(capacity_keys)))
    for row, key in enumerate(equality_groups):
        equality_projection[row, equality_index[key]] = 1
    for row, key in enumerate(capacity_groups):
        capacity_projection[row, capacity_index[key]] = 1
    equality_projection = equality_projection.tocsr()
    capacity_projection = capacity_projection.tocsr()
    projected_equalities = equalities.T @ equality_projection
    projected_capacities = capacities.T @ capacity_projection
    free_count = len(equality_keys)
    nonnegative_count = len(capacity_keys)
    inequalities = hstack([-projected_equalities, projected_equalities,
                            -projected_capacities], format="csr")
    projected_rhs = np.r_[equality_rhs @ equality_projection,
                          capacity_rhs @ capacity_projection]
    scalar = lil_matrix((1, 2 * free_count + nonnegative_count))
    scalar[0, :free_count] = projected_rhs[:free_count]
    scalar[0, free_count:2 * free_count] = -projected_rhs[:free_count]
    scalar[0, 2 * free_count:] = projected_rhs[free_count:]
    result = linprog(
        np.ones(2 * free_count + nonnegative_count),
        A_ub=inequalities, b_ub=np.zeros(variable_count),
        A_eq=scalar.tocsr(), b_eq=[-1], bounds=(0, None), method="highs")
    if not result.success:
        return False, len(equality_keys), len(capacity_keys), False, 0
    y_group = result.x[:free_count] - result.x[free_count:2 * free_count]
    z_group = result.x[2 * free_count:]
    nonzero = []
    for name, key in zip(equality_names, equality_groups):
        value = y_group[equality_index[key]]
        if abs(value) > 1e-8:
            nonzero.append((name, value))
    for name, key in zip(capacity_names, capacity_groups):
        value = z_group[capacity_index[key]]
        if value > 1e-8:
            nonzero.append((name, value))
    exact, _, denominator, _ = rational_farkas_audit(system, nonzero)
    return True, len(equality_keys), len(capacity_keys), exact, denominator


def label_load_formula_audit(data: dict) -> tuple[bool, dict[int, int]]:
    """Audit the fiber-load Fubini formula and its total-load identity."""
    _, censuses = root_signature_censuses(data)
    loads = {}
    valid = True
    for b in data["selected"]:
        census_sum = sum(sum(censuses[t][b]) for t in range(N))
        fiber_degree_sum = sum(len(data["candidates"][u]) for u in range(N)
                               if b in data["blocks"][u])
        valid &= census_sum == fiber_degree_sum
        loads[b] = fiber_degree_sum
    selected = set(data["selected"])
    multiplicity_total = sum(
        len(data["candidates"][u])
        * len(selected.intersection(data["blocks"][u]))
        for u in range(N))
    valid &= sum(loads.values()) == multiplicity_total
    return valid, loads


def affine_load_half_atom_dual(data: dict) -> tuple:
    """Test prices affine in L(b), with coefficients indexed by sigma,rho."""
    from scipy.sparse import hstack, vstack

    system = half_atom_primal_system(data)
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     capacity_names, _) = system
    signatures, censuses = root_signature_censuses(data)
    loads = {
        b: sum(len(data["candidates"][u]) for u in range(N)
               if b in data["blocks"][u])
        for b in data["selected"]
    }
    load_origin = round(sum(loads.values()) / len(loads))
    load_coordinates = {b: loads[b] - load_origin for b in loads}

    alpha_keys = sorted(set(signatures), key=repr)
    local_keys = sorted(set(
        (signatures[t], censuses[t][b])
        for t in range(N) for b in data["selected"]), key=repr)
    local_load_sets = {
        key: {loads[b] for t in range(N) for b in data["selected"]
              if (signatures[t], censuses[t][b]) == key}
        for key in local_keys
    }
    nonlinear_test_classes = sum(
        len(values) >= 3 for values in local_load_sets.values())
    alpha_index = {key: i for i, key in enumerate(alpha_keys)}
    local_index = {key: i for i, key in enumerate(local_keys)}
    alpha_count = len(alpha_keys)
    local_count = len(local_keys)
    coefficient_count = alpha_count + 4 * local_count

    equality_projection = lil_matrix(
        (len(equality_names), coefficient_count))
    for row, name in enumerate(equality_names):
        if name[0] == "row":
            equality_projection[row, alpha_index[signatures[name[1]]]] = 1
            continue
        t, b = name[1]
        index = local_index[(signatures[t], censuses[t][b])]
        equality_projection[row, alpha_count + 2 * index] = 1
        equality_projection[row, alpha_count + 2 * index + 1] = (
            load_coordinates[b])

    capacity_projection = lil_matrix(
        (len(capacity_names), coefficient_count))
    capacity_offset = alpha_count + 2 * local_count
    for row, (_, t, b) in enumerate(capacity_names):
        index = local_index[(signatures[t], censuses[t][b])]
        capacity_projection[row, capacity_offset + 2 * index] = 1
        capacity_projection[row, capacity_offset + 2 * index + 1] = (
            load_coordinates[b])
    equality_projection = equality_projection.tocsr()
    capacity_projection = capacity_projection.tocsr()

    route_prices = (equalities.T @ equality_projection
                    + capacities.T @ capacity_projection)
    inequalities = vstack([-route_prices, -capacity_projection], format="csr")
    scalar = (equality_rhs @ equality_projection
              + capacity_rhs @ capacity_projection)
    result = linprog(
        np.zeros(coefficient_count), A_ub=inequalities,
        b_ub=np.zeros(inequalities.shape[0]),
        A_eq=scalar.reshape(1, -1), b_eq=[-1],
        bounds=[(None, None)] * coefficient_count, method="highs")
    if not result.success:
        return False, alpha_count, local_count, nonlinear_test_classes, False, 0

    equality_values = equality_projection @ result.x
    capacity_values = capacity_projection @ result.x
    nonzero = [
        (name, float(value))
        for name, value in zip(equality_names, equality_values)
        if abs(value) > 1e-8
    ] + [
        (name, float(value))
        for name, value in zip(capacity_names, capacity_values)
        if value > 1e-8
    ]
    exact, _, denominator, _ = rational_farkas_audit(system, nonzero)
    return (True, alpha_count, local_count, nonlinear_test_classes, exact,
            denominator)


def common_affine_load_half_atom_dual(instances: list[dict]) -> tuple:
    """Test one shared affine-in-load price on a family of instances."""
    prepared = []
    alpha_keys = set()
    local_keys = set()
    instance_alpha_sets = []
    instance_local_sets = []
    for data in instances:
        signatures, censuses = root_signature_censuses(data)
        loads = {
            b: sum(len(data["candidates"][u]) for u in range(N)
                   if b in data["blocks"][u])
            for b in data["selected"]
        }
        prepared.append((data, signatures, censuses, loads))
        instance_alpha = set(signatures)
        instance_local = set(
            (signatures[t], censuses[t][b])
            for t in range(N) for b in data["selected"])
        instance_alpha_sets.append(instance_alpha)
        instance_local_sets.append(instance_local)
        alpha_keys.update(instance_alpha)
        local_keys.update(instance_local)
    alpha_keys = sorted(alpha_keys, key=repr)
    local_keys = sorted(local_keys, key=repr)
    alpha_index = {key: i for i, key in enumerate(alpha_keys)}
    local_index = {key: i for i, key in enumerate(local_keys)}
    alpha_count = len(alpha_keys)
    local_count = len(local_keys)
    shared_alpha_count = sum(
        sum(key in keys for keys in instance_alpha_sets) >= 2
        for key in alpha_keys)
    shared_local_count = sum(
        sum(key in keys for keys in instance_local_sets) >= 2
        for key in local_keys)
    coefficient_count = alpha_count + 4 * local_count
    capacity_offset = alpha_count + 2 * local_count
    inequality_blocks = []
    rhs_blocks = []

    # A fixed origin preserves a single affine function across all instances.
    load_origin = 75
    for data, signatures, censuses, loads in prepared:
        (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
         capacity_names, _) = half_atom_primal_system(data)
        equality_projection = lil_matrix(
            (len(equality_names), coefficient_count))
        for row, name in enumerate(equality_names):
            if name[0] == "row":
                equality_projection[
                    row, alpha_index[signatures[name[1]]]] = 1
                continue
            t, b = name[1]
            index = local_index[(signatures[t], censuses[t][b])]
            equality_projection[row, alpha_count + 2 * index] = 1
            equality_projection[row, alpha_count + 2 * index + 1] = (
                loads[b] - load_origin)
        capacity_projection = lil_matrix(
            (len(capacity_names), coefficient_count))
        for row, (_, t, b) in enumerate(capacity_names):
            index = local_index[(signatures[t], censuses[t][b])]
            capacity_projection[row, capacity_offset + 2 * index] = 1
            capacity_projection[row, capacity_offset + 2 * index + 1] = (
                loads[b] - load_origin)
        equality_projection = equality_projection.tocsr()
        capacity_projection = capacity_projection.tocsr()
        route_prices = (equalities.T @ equality_projection
                        + capacities.T @ capacity_projection)
        scalar = (equality_rhs @ equality_projection
                  + capacity_rhs @ capacity_projection)
        inequality_blocks.extend(
            [-route_prices, -capacity_projection,
             scalar.reshape(1, -1)])
        rhs_blocks.extend([
            np.zeros(route_prices.shape[0]),
            np.zeros(capacity_projection.shape[0]),
            np.array([-1.0]),
        ])
    inequalities = vstack(inequality_blocks, format="csr")
    result = linprog(
        np.zeros(coefficient_count), A_ub=inequalities,
        b_ub=np.concatenate(rhs_blocks),
        bounds=[(None, None)] * coefficient_count, method="highs",
        options={"time_limit": 300.0})
    return (result.success, len(instances), alpha_count, local_count,
            shared_alpha_count, shared_local_count, result.message)


def polynomial_collision_census_dual(data: dict, degree: int = 2) -> tuple:
    """Test a common low-degree polynomial potential on seven-state rows."""
    from scipy.sparse import hstack

    if degree not in (1, 2):
        raise ValueError("only linear and quadratic state potentials are supported")
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     _, _) = collision_census_primal_system(data)
    monomials = ([(coordinate,) for coordinate in range(7)]
                 + ([(left, right) for left in range(7)
                     for right in range(left, 7)] if degree == 2 else []))
    basis_count = 1 + len(monomials)
    latent_count = N + basis_count
    projection = lil_matrix((equalities.shape[0], latent_count))
    for t in range(N):
        projection[t, t] = 1
    for row, name in enumerate(equality_names[N:], start=N):
        state = name[1]
        values = [1.0]
        for indices in monomials:
            value = 1.0
            for coordinate in indices:
                value *= state[coordinate]
            values.append(value)
        for coordinate, value in enumerate(values):
            projection[row, N + coordinate] = value
    columns = equalities.T @ projection.tocsr()
    inequalities = hstack([-columns, -capacities.T], format='csr')
    latent_rhs = np.r_[equality_rhs[:N], np.zeros(basis_count)]
    scalar = np.r_[latent_rhs, capacity_rhs].reshape(1, -1)
    result = linprog(
        np.zeros(latent_count + capacities.shape[0]),
        A_ub=inequalities, b_ub=np.zeros(columns.shape[0]),
        A_eq=scalar, b_eq=[-1],
        bounds=[(None, None)] * latent_count
        + [(0, None)] * capacities.shape[0], method='highs')
    if not result.success:
        return False, result.message, ()
    coefficients = tuple(float(value) for value in result.x[N:N + basis_count])
    return True, result.message, coefficients


def categorical_collision_census_dual(
        data: dict, order: int = 2,
        extra_coordinate_sets: tuple[tuple[int, ...], ...] = ()) -> tuple:
    """Test additive one- or two-coordinate tables on seven-state rows."""
    from itertools import combinations
    from scipy.linalg import qr
    from scipy.sparse import hstack

    if order not in (1, 2):
        raise ValueError("only one- and two-coordinate tables are supported")
    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     _, _) = collision_census_primal_system(data)
    states = [name[1] for name in equality_names[N:]]
    coordinate_sets = [(coordinate,) for coordinate in range(7)]
    if order == 2:
        coordinate_sets += list(combinations(range(7), 2))
    coordinate_sets += list(extra_coordinate_sets)
    basis_keys = []
    for coordinates in coordinate_sets:
        values = sorted({tuple(state[c] for c in coordinates)
                         for state in states})
        basis_keys.extend((coordinates, value) for value in values)
    basis_index = {key: index for index, key in enumerate(basis_keys)}
    latent_count = N + len(basis_keys)
    projection = lil_matrix((equalities.shape[0], latent_count))
    for t in range(N):
        projection[t, t] = 1
    for row, name in enumerate(equality_names[N:], start=N):
        state = name[1]
        for coordinates in coordinate_sets:
            value = tuple(state[c] for c in coordinates)
            projection[row, N + basis_index[(coordinates, value)]] = 1
    # Lookup tables have many gauge dependencies (constants and lower-order
    # marginals repeat across tables).  Pivot a numerical basis of their exact
    # state-evaluation span before presenting the dual to HiGHS.
    state_features = projection[N:, N:].toarray()
    _, triangular, pivots = qr(state_features, mode='economic', pivoting=True)
    diagonal = np.abs(np.diag(triangular))
    tolerance = (max(state_features.shape) * np.finfo(float).eps
                 * (diagonal[0] if len(diagonal) else 0.0))
    rank = int(np.sum(diagonal > tolerance))
    selected = sorted(int(pivot) for pivot in pivots[:rank])
    reduced = lil_matrix((equalities.shape[0], N + rank))
    reduced[:N, :N] = projection[:N, :N]
    reduced[N:, N:] = projection[N:, N + np.array(selected)]
    projection = reduced
    latent_count = N + rank
    columns = equalities.T @ projection.tocsr()
    inequalities = hstack([-columns, -capacities.T], format='csr')
    latent_rhs = np.r_[equality_rhs[:N], np.zeros(rank)]
    scalar = np.r_[latent_rhs, capacity_rhs].reshape(1, -1)
    result = linprog(
        np.zeros(latent_count + capacities.shape[0]),
        A_ub=inequalities, b_ub=np.zeros(columns.shape[0]),
        A_eq=scalar, b_eq=[-1],
        bounds=[(None, None)] * latent_count
        + [(0, None)] * capacities.shape[0], method='highs')
    return result.success, result.message, rank


def integer_full_bundle_dual(data: dict, time_limit: float = 60) -> tuple:
    """Search directly for an integer Farkas certificate."""
    from scipy.sparse import hstack

    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     capacity_names, _) = full_bundle_primal_system(data)
    equality_count = equalities.shape[0]
    capacity_count = capacities.shape[0]
    columns = hstack([equalities.T, -equalities.T, capacities.T], format='csr')
    scalar = lil_matrix((1, 2 * equality_count + capacity_count))
    scalar[0, :equality_count] = equality_rhs
    scalar[0, equality_count:2 * equality_count] = -equality_rhs
    scalar[0, 2 * equality_count:] = capacity_rhs
    constraints = vstack([columns, scalar.tocsr()], format='csr')
    result = milp(
        np.ones(constraints.shape[1]), integrality=np.ones(constraints.shape[1]),
        bounds=Bounds(np.zeros(constraints.shape[1]), np.full(constraints.shape[1], np.inf)),
        constraints=LinearConstraint(
            constraints,
            np.r_[np.zeros(columns.shape[0]), -np.inf],
            np.r_[np.full(columns.shape[0], np.inf), -1]),
        options={'time_limit': time_limit})
    if result.x is None:
        return False, result.message, [], False, 0, 0
    rounded = np.rint(result.x).astype(int)
    y = (rounded[:equality_count] -
         rounded[equality_count:2 * equality_count])
    z = rounded[2 * equality_count:]
    column_values = equalities.T @ y + capacities.T @ z
    scalar_value = int(equality_rhs @ y + capacity_rhs @ z)
    exact = bool(np.max(np.abs(result.x - rounded), initial=0) < 1e-7
                 and np.all(column_values >= 0) and scalar_value < 0)
    nonzero = ([(equality_names[index], int(value))
                for index, value in enumerate(y) if value]
               + [(capacity_names[index], int(value))
                  for index, value in enumerate(z) if value])
    return (True, result.message, nonzero, exact, scalar_value,
            int(np.min(column_values, initial=0)))


def bounded_integer_full_bundle_dual(
        data: dict, coefficient_bound: int = 2,
        time_limit: float = 60) -> tuple:
    """Seek any exact integer dual with every coefficient bounded."""
    from scipy.sparse import hstack

    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     capacity_names, _) = full_bundle_primal_system(data)
    equality_count = equalities.shape[0]
    capacity_count = capacities.shape[0]
    columns = hstack([equalities.T, -equalities.T, capacities.T], format='csr')
    scalar = lil_matrix((1, 2 * equality_count + capacity_count))
    scalar[0, :equality_count] = equality_rhs
    scalar[0, equality_count:2 * equality_count] = -equality_rhs
    scalar[0, 2 * equality_count:] = capacity_rhs
    constraints = vstack([columns, scalar.tocsr()], format='csr')
    variable_count = constraints.shape[1]
    result = milp(
        np.zeros(variable_count), integrality=np.ones(variable_count),
        bounds=Bounds(np.zeros(variable_count),
                      np.full(variable_count, coefficient_bound)),
        constraints=LinearConstraint(
            constraints,
            np.r_[np.zeros(columns.shape[0]), -np.inf],
            np.r_[np.full(columns.shape[0], np.inf), -1]),
        options={'time_limit': time_limit})
    if result.x is None:
        return False, result.message, [], False, 0, 0
    rounded = np.rint(result.x).astype(int)
    y = (rounded[:equality_count]
         - rounded[equality_count:2 * equality_count])
    z = rounded[2 * equality_count:]
    column_values = equalities.T @ y + capacities.T @ z
    scalar_value = int(equality_rhs @ y + capacity_rhs @ z)
    exact = bool(np.max(np.abs(result.x - rounded), initial=0) < 1e-7
                 and np.all(column_values >= 0) and scalar_value < 0
                 and np.max(np.abs(y), initial=0) <= coefficient_bound
                 and np.max(z, initial=0) <= coefficient_bound)
    nonzero = ([(equality_names[index], int(value))
                for index, value in enumerate(y) if value]
               + [(capacity_names[index], int(value))
                  for index, value in enumerate(z) if value])
    return (True, result.message, nonzero, exact, scalar_value,
            int(np.min(column_values, initial=0)))


def integer_dual_pivot_profile(data: dict, nonzero: list[tuple]) -> tuple:
    """Summarize pivot labels hitting every negative-demand support."""
    demand_roots = {name[1] for name, value in nonzero
                    if name[0] == 'row' and value < 0}
    supports = [data['blocks'][t] & data['selected']
                for t in sorted(demand_roots)]
    pivot_covers = []
    for size in range(1, len(data['selected']) + 1):
        pivot_covers = [cover for cover in combinations(sorted(data['selected']), size)
                        if all(set(cover) & support for support in supports)]
        if pivot_covers:
            break
    pivots = set(pivot_covers[0]) if len(pivot_covers) == 1 else set()
    pivot_occurrences = tuple(
        (b, tuple(t for t in range(N) if b in data['blocks'][t]),
         tuple(t for t in sorted(demand_roots) if b in data['blocks'][t]))
        for b in sorted(pivots))
    predicted_demands = tuple(t for t in range(N)
                              if data['types'][t] in (0, 1)
                              and data['blocks'][t] & pivots)
    demand_tuple = tuple(sorted(demand_roots))
    relay_capacities = [(name[1], name[2], value) for name, value in nonzero
                        if name[0] == 'capacity'
                        and name[1] not in demand_roots
                        and name[2] not in pivots]
    return (demand_tuple, tuple(pivot_covers), pivot_occurrences,
            set(demand_tuple) <= set(predicted_demands),
            predicted_demands == demand_tuple,
            tuple(relay_capacities))


def integer_dual_slack_profile(data: dict, nonzero: list[tuple]) -> tuple:
    """List the exceptional positive-slack candidate inequalities."""
    (equalities, _, capacities, _, equality_names, capacity_names,
     _) = full_bundle_primal_system(data)
    equality_values = dict(nonzero)
    capacity_values = dict(nonzero)
    y = np.array([equality_values.get(name, 0) for name in equality_names])
    z = np.array([capacity_values.get(name, 0) for name in capacity_names])
    values = np.asarray(equalities.T @ y + capacities.T @ z).ravel()
    exceptions = []
    column = 0
    for t in range(N):
        for u in data['candidates'][t]:
            value = int(values[column])
            if value:
                exceptions.append((t, u, value))
            column += 1
    return (len(values), tuple(sorted(Counter(map(int, values)).items())),
            tuple(exceptions))


def fractional_system_slack_profile(system: tuple, nonzero: list[tuple]) -> tuple:
    """Count tight and positive columns of a floating Farkas dual."""
    (equalities, _, capacities, _, equality_names, capacity_names,
     _) = system
    values_by_name = dict(nonzero)
    y = np.array([values_by_name.get(name, 0.0) for name in equality_names])
    z = np.array([values_by_name.get(name, 0.0) for name in capacity_names])
    values = np.asarray(equalities.T @ y + capacities.T @ z).ravel()
    tight = int(np.sum(np.abs(values) <= 1e-7))
    positive = int(np.sum(values > 1e-7))
    return len(values), tight, positive, float(np.max(values, initial=0))


def fractional_dual_slack_profile(data: dict, nonzero: list[tuple]) -> tuple:
    return fractional_system_slack_profile(full_bundle_primal_system(data),
                                           nonzero)


def linear_state_bundle_dual(data: dict) -> tuple[bool, str]:
    """Test external-label potentials linear in signature and role census."""
    from scipy.sparse import hstack

    (equalities, equality_rhs, capacities, capacity_rhs, equality_names,
     _, _) = full_bundle_primal_system(data)
    # One constant, four signature coordinates, and five census coordinates.
    basis_count = 10
    latent_count = N + basis_count
    projection = lil_matrix((equalities.shape[0], latent_count))
    for t in range(N):
        projection[t, t] = 1
    for row, name in enumerate(equality_names[N:], start=N):
        feature = name[1]
        if feature[0] != 'bundle' or feature[2] != 0:
            continue
        values = (1,) + tuple(feature[1]) + tuple(feature[3])
        for coordinate, value in enumerate(values):
            projection[row, N + coordinate] = value
    columns = equalities.T @ projection.tocsr()
    inequalities = hstack([-columns, -capacities.T], format='csr')
    latent_rhs = np.r_[equality_rhs[:N], np.zeros(basis_count)]
    scalar = np.r_[latent_rhs, capacity_rhs].reshape(1, -1)
    result = linprog(
        np.zeros(latent_count + capacities.shape[0]),
        A_ub=inequalities, b_ub=np.zeros(columns.shape[0]),
        A_eq=scalar, b_eq=[-1],
        bounds=[(None, None)] * latent_count
        + [(0, None)] * capacities.shape[0], method='highs')
    return result.success, result.message


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
    parser.add_argument("--audit-bundle-deletion", action="store_true",
                        help="audit paired external deletion losses")
    parser.add_argument("--audit-zero-loss-restriction", action="store_true",
                        help="test Hall after retaining only external and Z transitions")
    parser.add_argument("--audit-full-bundle-primal", action="store_true",
                        help="test normalized matching flow with bundle equality")
    parser.add_argument("--audit-bundle-primal-ablation", action="store_true",
                        help="ablate alpha/external/internal primal equalities")
    parser.add_argument("--audit-external-coarsening", action="store_true",
                        help="drop coordinates from external bundle states")
    parser.add_argument("--audit-full-bundle-dual", action="store_true",
                        help="extract sparse duals for restricted-Hall survivors")
    parser.add_argument("--audit-collision-census-dual", action="store_true",
                        help="extract duals for seven-coordinate external states")
    parser.add_argument("--audit-collision-census-core", action="store_true",
                        help="greedily minimize seven-state infeasible equations")
    parser.add_argument("--audit-polynomial-collision-census-dual",
                        action="store_true",
                        help="test linear/quadratic seven-state potentials")
    parser.add_argument("--audit-categorical-collision-census-dual",
                        action="store_true",
                        help="test one-/two-coordinate state lookup tables")
    parser.add_argument("--audit-triple-categorical-augmentations",
                        action="store_true",
                        help="add each coordinate triple to pairwise tables")
    parser.add_argument("--categorical-extra-triple", default="",
                        help="comma-separated coordinates for one triple table")
    parser.add_argument("--audit-double-label-flag-primal", action="store_true",
                        help="test collision-witness flag conservation")
    parser.add_argument("--audit-double-label-flag-private", action="store_true",
                        help="check private rows in unordered flag boundaries")
    parser.add_argument("--audit-half-atom-primal", action="store_true",
                        help="test abstract root-label atom conservation")
    parser.add_argument("--audit-half-atom-dual", action="store_true",
                        help="extract exact rational half-atom certificates")
    parser.add_argument("--audit-half-atom-projections", action="store_true",
                        help="test invariant root/label price factorizations")
    parser.add_argument("--audit-affine-load-dual", action="store_true",
                        help="test half-atom prices affine in fiber load")
    parser.add_argument("--audit-common-affine-load-dual", action="store_true",
                        help="test one affine load price across all survivors")
    parser.add_argument("--audit-label-load-formula", action="store_true",
                        help="verify the fiber-degree formula for L(b)")
    parser.add_argument("--print-full-dual", action="store_true",
                        help="do not truncate fractional dual diagnostics")
    parser.add_argument("--audit-integer-bundle-dual", action="store_true",
                        help="search integer duals for restricted-Hall survivors")
    parser.add_argument("--audit-bounded-bundle-dual", action="store_true",
                        help="seek coefficient-bounded integer survivor duals")
    parser.add_argument("--integer-dual-time-limit", type=float, default=60,
                        help="seconds per integer bundle-dual survivor")
    parser.add_argument("--dual-seed-filter", default="",
                        help="comma-separated seed numbers to analyze in dual modes")
    parser.add_argument("--bounded-dual-coefficient", type=int, default=2,
                        help="absolute coefficient bound for bounded dual mode")
    parser.add_argument("--audit-linear-bundle-dual", action="store_true",
                        help="test linear state-potential duals on survivors")
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
    dual_seed_filter = ({int(value) for value in args.dual_seed_filter.split(',')
                         if value} if args.dual_seed_filter else set())
    if os.environ.get('PYTHONHASHSEED') != '0':
        print("warning: set PYTHONHASHSEED=0 before launch for reproducible "
              "outer-model seed labels", file=sys.stderr)
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
        total_nonprivate_bundle = 0
        total_nonprivate_external = 0
        for label, candidate in all_data:
            (columns, rank, missing, nonprivate,
             nonprivate_bundle,
             nonprivate_external) = bundle_rank_audit(candidate)
            total_columns += columns
            total_rank += rank
            total_missing += len(missing)
            total_nonprivate += len(nonprivate)
            total_nonprivate_bundle += len(nonprivate_bundle)
            total_nonprivate_external += len(nonprivate_external)
            branch, seed_number, colors = label
            print(f"bundle_rank branch={branch} seed={seed_number} "
                  f"colors={colors} columns={columns} rank={rank} "
                  f"missing_reverse={missing} nonprivate={nonprivate} "
                  f"nonprivate_bundle={nonprivate_bundle} "
                  f"nonprivate_external={nonprivate_external}")
        print(f"bundle_rank_total_columns={total_columns} "
              f"total_rank={total_rank} missing_reverse={total_missing} "
              f"nonprivate={total_nonprivate} "
              f"nonprivate_bundle={total_nonprivate_bundle} "
              f"nonprivate_external={total_nonprivate_external}")
        audit_failed |= (total_rank != total_columns or total_missing > 0
                         or total_nonprivate > 0
                         or total_nonprivate_bundle > 0)
    if args.audit_bundle_deletion:
        total_losses = Counter()
        total_zero = 0
        total_forced_both = 0
        total_shapes = Counter()
        for label, candidate in all_data:
            losses, zero_pairs, shapes = bundle_deletion_audit(candidate)
            total_losses.update(losses)
            total_zero += len(zero_pairs)
            total_forced_both += sum(forward and reverse
                                     for _, _, forward, reverse in zero_pairs)
            total_shapes.update(shapes)
            branch, seed_number, colors = label
            print(f"bundle_deletion branch={branch} seed={seed_number} "
                  f"colors={colors} losses={dict(losses)} "
                  f"zero_pairs={zero_pairs} zero_shapes={shapes}")
        print(f"bundle_deletion_total_losses={dict(total_losses)} "
              f"zero_pairs={total_zero} forced_both={total_forced_both} "
              f"zero_shapes={dict(total_shapes)}")
    if args.audit_zero_loss_restriction:
        bad_count_distribution = Counter()
        survivors = []
        for label, candidate in all_data:
            zero_edges, bad_rows = zero_loss_restricted_hall_audit(candidate)
            bad_count_distribution[len(bad_rows)] += 1
            branch, seed_number, colors = label
            print(f"zero_loss_restriction branch={branch} seed={seed_number} "
                  f"colors={colors} zero_edges={zero_edges} bad_rows={bad_rows}")
            if not bad_rows:
                survivors.append(label)
        print(f"zero_loss_restriction_bad_count_distribution="
              f"{dict(bad_count_distribution)} survivors={survivors}")
    if args.audit_full_bundle_primal:
        feasible_labels = []
        for label, candidate in all_data:
            feasible, message = full_bundle_primal_feasible(candidate)
            branch, seed_number, colors = label
            print(f"full_bundle_primal branch={branch} seed={seed_number} "
                  f"colors={colors} feasible={feasible} message={message}")
            if feasible:
                feasible_labels.append(label)
        print(f"full_bundle_primal_feasible={feasible_labels}")
    if args.audit_bundle_primal_ablation:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            branch, seed_number, colors = label
            print(f"bundle_primal_ablation branch={branch} seed={seed_number} "
                  f"colors={colors} feasible="
                  f"{full_bundle_primal_ablation(candidate)}")
    if args.audit_external_coarsening:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            branch, seed_number, colors = label
            print(f"external_coarsening branch={branch} seed={seed_number} "
                  f"colors={colors} feasible="
                  f"{external_bundle_coarsening_audit(candidate)}")
    if args.audit_full_bundle_dual:
        dual_labels = []
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            success, norm, nonzero, exact = sparse_full_bundle_dual(candidate)
            branch, seed_number, colors = label
            displayed = nonzero if exact or args.print_full_dual else nonzero[:20]
            print(f"full_bundle_dual branch={branch} seed={seed_number} "
                  f"colors={colors} success={success} l1={norm} "
                  f"nonzero_count={len(nonzero)} nonzero={displayed} "
                  f"nonzero_truncated={not exact and not args.print_full_dual and len(nonzero) > 20} "
                  f"exact_integer={exact}")
            if success:
                print(f"full_bundle_dual_slacks branch={branch} "
                      f"seed={seed_number} colors={colors} "
                      f"profile={fractional_dual_slack_profile(candidate, nonzero)}")
            dual_labels.append((label, success, exact, len(nonzero)))
        print(f"full_bundle_dual_survivors={dual_labels}")
        audit_failed |= any(not success or not exact
                            for _, success, exact, _ in dual_labels)
    if args.audit_collision_census_dual:
        projected_labels = []
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            success, norm, nonzero, exact = sparse_collision_census_dual(candidate)
            system = collision_census_primal_system(candidate)
            branch, seed_number, colors = label
            print(f"collision_census_dual branch={branch} seed={seed_number} "
                  f"colors={colors} success={success} l1={norm} "
                  f"nonzero_count={len(nonzero)} exact_integer={exact} "
                  f"slacks={fractional_system_slack_profile(system, nonzero)}")
            projected_labels.append((label, success, exact, len(nonzero)))
        print(f"collision_census_dual_survivors={projected_labels}")
    if args.audit_collision_census_core:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            branch, seed_number, colors = label
            print(f"collision_census_core branch={branch} seed={seed_number} "
                  f"colors={colors} core="
                  f"{collision_census_infeasible_core(candidate)}")
    if args.audit_polynomial_collision_census_dual:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            branch, seed_number, colors = label
            for degree in (1, 2):
                success, message, coefficients = (
                    polynomial_collision_census_dual(candidate, degree))
                nonzero = sum(abs(value) > 1e-8 for value in coefficients)
                print(f"polynomial_collision_census_dual branch={branch} "
                      f"seed={seed_number} colors={colors} degree={degree} "
                      f"success={success} coefficient_nonzero={nonzero} "
                      f"message={message}")
    if args.audit_categorical_collision_census_dual:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            branch, seed_number, colors = label
            for order in (1, 2):
                success, message, basis_count = (
                    categorical_collision_census_dual(candidate, order))
                print(f"categorical_collision_census_dual branch={branch} "
                      f"seed={seed_number} colors={colors} order={order} "
                      f"success={success} basis_count={basis_count} "
                      f"message={message}")
    if args.audit_triple_categorical_augmentations:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            branch, seed_number, colors = label
            successful = []
            infeasible = []
            indeterminate = []
            for coordinates in combinations(range(7), 3):
                success, message, basis_count = categorical_collision_census_dual(
                    candidate, 2, (coordinates,))
                if success:
                    successful.append((coordinates, basis_count))
                elif "model_status is Infeasible" in message:
                    infeasible.append(coordinates)
                else:
                    indeterminate.append((coordinates, message))
            print(f"triple_categorical_augmentations branch={branch} "
                  f"seed={seed_number} colors={colors} "
                  f"successful={successful} infeasible={infeasible} "
                  f"indeterminate={indeterminate}")
    if args.categorical_extra_triple:
        try:
            coordinates = tuple(int(value) for value in
                                args.categorical_extra_triple.split(','))
        except ValueError:
            parser.error("--categorical-extra-triple requires integers")
        if len(coordinates) != 3 or len(set(coordinates)) != 3 or not all(
                0 <= coordinate < 7 for coordinate in coordinates):
            parser.error("--categorical-extra-triple requires three distinct "
                         "coordinates in 0,...,6")
        coordinates = tuple(sorted(coordinates))
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            success, message, basis_count = categorical_collision_census_dual(
                candidate, 2, (coordinates,))
            branch, seed_number, colors = label
            print(f"fixed_triple_categorical_dual branch={branch} "
                  f"seed={seed_number} colors={colors} "
                  f"coordinates={coordinates} success={success} "
                  f"basis_count={basis_count} message={message}")
    if args.audit_double_label_flag_primal:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            branch, seed_number, colors = label
            for mode in ("roles", "equality", "transported", "witness",
                         "unordered", "full"):
                success, flag_count, message = double_label_flag_primal_audit(
                    candidate, mode)
                print(f"double_label_flag_primal branch={branch} "
                      f"seed={seed_number} colors={colors} mode={mode} "
                      f"feasible={success} flag_count={flag_count} "
                      f"message={message}")
    if args.audit_double_label_flag_private:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            (columns, rank, missing_reverse, without_private,
             duplicate_excess, duplicate_groups,
             fundamental_supports, small_relations,
             triangle_count, triangle_rank, atom_rank) = (
                double_label_flag_private_audit(candidate))
            branch, seed_number, colors = label
            signatures, _ = root_signature_censuses(candidate)
            relation_vertices = sorted({vertex
                                        for relation in small_relations
                                        for edge, _ in relation
                                        for vertex in edge})
            relation_profiles = [
                (vertex, TYPE_NAMES[candidate["types"][vertex]],
                 tuple(sorted(candidate["blocks"][vertex] &
                              candidate["selected"])), signatures[vertex])
                for vertex in relation_vertices]
            print(f"double_label_flag_private branch={branch} "
                  f"seed={seed_number} colors={colors} columns={columns} "
                  f"rank={rank} "
                  f"missing_reverse={missing_reverse} "
                  f"without_private_count={len(without_private)} "
                  f"duplicate_excess={duplicate_excess} "
                  f"duplicate_groups={duplicate_groups} "
                  f"fundamental_supports={fundamental_supports} "
                  f"small_relations={small_relations} "
                  f"support_triangles={triangle_count} "
                  f"support_triangle_rank={triangle_rank} "
                  f"atom_rank={atom_rank} "
                  f"atom_nullity={columns - atom_rank} "
                  f"relation_profiles={relation_profiles} "
                  f"without_private={without_private[:20]}")
    if args.audit_half_atom_primal:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            feasible, atom_count, message = half_atom_primal_audit(candidate)
            branch, seed_number, colors = label
            print(f"half_atom_primal branch={branch} seed={seed_number} "
                  f"colors={colors} feasible={feasible} "
                  f"atom_count={atom_count} message={message}")
    if args.audit_half_atom_dual:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            success, norm, nonzero, integer, rational = (
                sparse_half_atom_dual(candidate))
            exact, scalar, denominator, minimum_slack = rational
            branch, seed_number, colors = label
            print(f"half_atom_dual branch={branch} seed={seed_number} "
                  f"colors={colors} success={success} l1={norm} "
                  f"nonzero_count={len(nonzero)} integer={integer} "
                  f"exact_rational={exact} scalar={scalar} "
                  f"max_denominator={denominator} "
                  f"minimum_slack={minimum_slack}")
    if args.audit_half_atom_projections:
        modes = ("type-color", "signature-color", "census-color",
                 "root-color", "type-label", "signature-label",
                 "census-label", "signature-loadsum", "root-loadsum",
                 "census-loadsum", "census-loadparity",
                 "census-loadsign", "census-loadsignparity")
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            branch, seed_number, colors = label
            results = {mode: projected_half_atom_dual(candidate, mode)
                       for mode in modes}
            print(f"half_atom_projections branch={branch} seed={seed_number} "
                  f"colors={colors} results={results}")
    if args.audit_label_load_formula:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            valid, loads = label_load_formula_audit(candidate)
            branch, seed_number, colors = label
            print(f"label_load_formula branch={branch} seed={seed_number} "
                  f"colors={colors} valid={valid} "
                  f"load_multiset={sorted(Counter(loads.values()).items())}")
    if args.audit_affine_load_dual:
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            (success, alpha_count, local_count, nonlinear_test_classes,
             exact, denominator) = (
                affine_load_half_atom_dual(candidate))
            branch, seed_number, colors = label
            print(f"affine_load_dual branch={branch} seed={seed_number} "
                  f"colors={colors} success={success} "
                  f"alpha_classes={alpha_count} local_classes={local_count} "
                  f"nonlinear_test_classes={nonlinear_test_classes} "
                  f"exact_rational={exact} max_denominator={denominator}")
    if args.audit_common_affine_load_dual:
        survivors = []
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if not bad_rows:
                survivors.append(candidate)
        result = common_affine_load_half_atom_dual(survivors)
        print(f"common_affine_load_dual success={result[0]} "
              f"instances={result[1]} alpha_classes={result[2]} "
              f"local_classes={result[3]} shared_alpha_classes={result[4]} "
              f"shared_local_classes={result[5]} message={result[6]}")
    if args.audit_integer_bundle_dual:
        integer_labels = []
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            (success, message, nonzero, exact, scalar,
             min_column) = integer_full_bundle_dual(
                 candidate, args.integer_dual_time_limit)
            branch, seed_number, colors = label
            print(f"integer_bundle_dual branch={branch} seed={seed_number} "
                  f"colors={colors} success={success} exact={exact} "
                  f"scalar={scalar} min_column={min_column} "
                  f"nonzero_count={len(nonzero)} message={message} "
                  f"nonzero={nonzero if exact else nonzero[:20]}")
            if exact:
                print(f"integer_bundle_pivots branch={branch} "
                      f"seed={seed_number} colors={colors} "
                      f"profile={integer_dual_pivot_profile(candidate, nonzero)}")
                print(f"integer_bundle_slacks branch={branch} "
                      f"seed={seed_number} colors={colors} "
                      f"profile={integer_dual_slack_profile(candidate, nonzero)}")
            integer_labels.append((label, success, exact, len(nonzero)))
        print(f"integer_bundle_dual_survivors={integer_labels}")
        audit_failed |= any(not success or not exact
                            for _, success, exact, _ in integer_labels)
    if args.audit_bounded_bundle_dual:
        bounded_labels = []
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            (success, message, nonzero, exact, scalar,
             min_column) = bounded_integer_full_bundle_dual(
                 candidate, args.bounded_dual_coefficient,
                 args.integer_dual_time_limit)
            branch, seed_number, colors = label
            print(f"bounded_bundle_dual branch={branch} seed={seed_number} "
                  f"colors={colors} success={success} exact={exact} "
                  f"scalar={scalar} min_column={min_column} "
                  f"nonzero_count={len(nonzero)} message={message}")
            if exact:
                print(f"bounded_bundle_slacks branch={branch} "
                      f"seed={seed_number} colors={colors} "
                      f"profile={integer_dual_slack_profile(candidate, nonzero)}")
            bounded_labels.append((label, success, exact, len(nonzero)))
        print(f"bounded_bundle_dual_survivors={bounded_labels}")
        audit_failed |= any(not success or not exact
                            for _, success, exact, _ in bounded_labels)
    if args.audit_linear_bundle_dual:
        linear_labels = []
        for label, candidate in all_data:
            if dual_seed_filter and label[1] not in dual_seed_filter:
                continue
            _, bad_rows = zero_loss_restricted_hall_audit(candidate)
            if bad_rows:
                continue
            success, message = linear_state_bundle_dual(candidate)
            branch, seed_number, colors = label
            print(f"linear_bundle_dual branch={branch} seed={seed_number} "
                  f"colors={colors} success={success} message={message}")
            linear_labels.append((label, success))
        print(f"linear_bundle_dual_survivors={linear_labels}")
    for branch, seed_number, colors, bad_rows in hall_labels:
        print(f"local_hall branch={branch} seed={seed_number} "
              f"colors={colors} rows={bad_rows}")
    if (args.audit_flat_signatures or args.audit_bundle_boundaries
            or args.audit_bundle_pairs or args.audit_bundle_triples
            or args.audit_bundle_rank or args.audit_bundle_deletion
            or args.audit_zero_loss_restriction
            or args.audit_full_bundle_primal or args.audit_bundle_primal_ablation
            or args.audit_external_coarsening
            or args.audit_full_bundle_dual
            or args.audit_collision_census_dual
            or args.audit_collision_census_core
            or args.audit_polynomial_collision_census_dual
            or args.audit_categorical_collision_census_dual
            or args.audit_triple_categorical_augmentations
            or args.categorical_extra_triple
            or args.audit_double_label_flag_primal
            or args.audit_double_label_flag_private
            or args.audit_half_atom_primal
            or args.audit_half_atom_dual
            or args.audit_half_atom_projections
            or args.audit_affine_load_dual
            or args.audit_common_affine_load_dual
            or args.audit_label_load_formula
            or args.audit_integer_bundle_dual
            or args.audit_bounded_bundle_dual
            or args.audit_linear_bundle_dual):
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
