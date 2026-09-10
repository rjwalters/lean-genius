#!/usr/bin/env python3
"""Decode an H1 SAT candidate and independently check its 49-vertex graph."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import verify_dimacs_model as model_checker
from verify_dimacs_model import VerificationError, read_model, verify


def edge_prefix(profile):
    """Mirror only pre-counter edge allocation; stop once all780 edges have IDs.

Source: Erdos85OneHighFamilyCnfGenerator.{InternalUnits,BaseUnits,C4Clauses}.
The prefix is checked clause-for-clause against the actual input before decoding.
"""
    if type(profile) is not int or not 0 <= profile <= 4:
        raise VerificationError('H1 profile must be0..4')
    ids, clauses = {}, []
    def edge(i, j):
        key = tuple(sorted((i, j)))
        if key not in ids:
            ids[key] = len(ids) + 1
        return ids[key]
    for b in range(8):
        two = not (b % 2 == 0 and b // 2 < profile)
        for i, j in itertools.combinations(range(5), 2):
            variable = edge(5*b+i, 5*b+j)
            present = (i, j) == (0, 1) or (two and (i, j) == (2, 3))
            clauses.append([variable if present else -variable])
    for b in (0, 2, 4, 6):
        for i in range(5):
            for j in range(5):
                clauses.append([-edge(5*b+i, 5*(b+1)+j)])
    for i, j in itertools.combinations(range(40), 2):
        others = [w for w in range(40) if w not in (i, j)]
        mids = ((w,) for w in others) if i//5 == j//5 else itertools.combinations(others, 2)
        for pair in mids:
            clauses.append([-edge(v, w) for w in pair for v in (i, j)])
            if len(ids) == 780:
                assert set(ids) == set(itertools.combinations(range(40), 2))
                return ids, clauses
    raise VerificationError('Incomplete edge allocation')


def verify_prefix(path, profile):
    ids, expected = edge_prefix(profile)
    digest = hashlib.sha256()
    count, header = 0, None
    with Path(path).open('rb') as source:
        for raw in source:
            digest.update(raw)
            line = raw.strip()
            if not line or line.startswith(b'c'):
                continue
            fields = line.split()
            if fields[0] == b'p':
                if header is not None or count or len(fields) != 4 or fields[1] != b'cnf':
                    raise VerificationError('Invalid CNF header')
                header = tuple(map(int, fields[2:]))
                continue
            if header is None:
                raise VerificationError('CNF clause before header')
            if count < len(expected):
                if fields != [str(v).encode() for v in expected[count]] + [b'0']:
                    raise VerificationError(f'H1 edge-ID prefix mismatch at clause{count+1}')
            count += 1
    if header is None or count < len(expected):
        raise VerificationError('Truncated H1 edge-ID prefix')
    return ids, digest.hexdigest(), len(expected)


def reconstruct(assignment, ids):
    if set(ids) != set(itertools.combinations(range(40), 2)):
        raise VerificationError('Incomplete edge map')
    edges = []
    for pair, variable in ids.items():
        if variable >= len(assignment) or type(assignment[variable]) is not bool:
            raise VerificationError('Missing graph-edge assignment')
        if assignment[variable]:
            edges.append(pair)
    # 0..39: eight five-vertex branches;40..47: root neighbors;48: unique high.
    edges += [(i, 40+i//5) for i in range(40)]
    edges += [(40+b, 41+b) for b in (0, 2, 4, 6)]
    edges += [(40+b, 48) for b in range(8)]
    return sorted(edges)


def graph_stats(order, edges):
    neighbors = [set() for _ in range(order)]
    for a, b in edges:
        if not (type(a) is int and type(b) is int and 0 <= a < b < order):
            raise VerificationError('Graph edge out of range, looped or unordered')
        if b in neighbors[a]:
            raise VerificationError('Duplicate graph edge')
        neighbors[a].add(b)
        neighbors[b].add(a)
    degrees = list(map(len, neighbors))
    rectangle = None
    maximum = 0
    for a, b in itertools.combinations(range(order), 2):
        common = sorted(neighbors[a] & neighbors[b])
        maximum = max(maximum, len(common))
        if len(common) >= 2 and rectangle is None:
            rectangle = [a, common[0], b, common[1]]
    return {'order': order, 'edges': len(edges), 'degrees': degrees,
            'minimum_degree': min(degrees), 'maximum_common_neighbors': maximum,
            'c4_free': rectangle is None, 'four_cycle': rectangle}


class GraphDecodeError(VerificationError):
    def __init__(self, message, evidence):
        super().__init__(message)
        self.evidence = evidence


def require_h1_graph(edges):
    stats = graph_stats(49, edges)
    if (not stats['c4_free'] or stats['minimum_degree'] < 7
            or stats['degrees'] != [7]*48 + [8]):
        raise GraphDecodeError('Decoded graph fails the H1 degree/C4 requirements',
            {'status': 'GRAPH_DECODE_ERROR', 'graph': stats, 'edge_list': edges,
             'scope': 'Rejected decoded candidate; never an UNSAT inference.'})
    return stats


def verify_candidate(cnf, model, profile, expected_cnf_sha256):
    # Bind every pass by content hash. The returned graph is also checked directly.
    ids, prefix_sha, prefix_count = verify_prefix(cnf, profile)
    if prefix_sha != expected_cnf_sha256:
        raise VerificationError('CNF identity mismatch')
    # Reject absurd/out-of-range model IDs before the existing complete-model reader allocates.
    with Path(cnf).open('rb') as source:
        header = next(raw.split() for raw in source if raw.startswith(b'p cnf '))
    bound = int(header[2])
    with Path(model).open('rb') as source:
        for raw in source:
            fields = raw.split()
            if fields[:1] == [b'v'] and any(abs(int(x)) > bound for x in fields[1:]):
                raise VerificationError('Model literal exceeds CNF header')
    variables, clauses, cnf_sha, model_sha = verify(Path(cnf), Path(model))
    assignment, decoded_sha = read_model(Path(model))
    if cnf_sha != prefix_sha or decoded_sha != model_sha:
        raise VerificationError('Input changed between verification passes')
    edges = reconstruct(assignment, ids)
    try:
        stats = require_h1_graph(edges)
    except GraphDecodeError as error:
        error.evidence.update(cnf_sha256=cnf_sha, model_sha256=model_sha, profile=profile)
        raise
    return {'status': 'GRAPH_WITNESS_VERIFIED', 'sector': 'H1', 'profile': profile,
            'cnf_sha256': cnf_sha, 'model_sha256': model_sha,
            'decoder_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'model_checker_sha256': hashlib.sha256(Path(model_checker.__file__).read_bytes()).hexdigest(),
            'cnf_variables': variables, 'cnf_clauses': clauses,
            'edge_map_prefix_clauses': prefix_count, 'graph': stats, 'edge_list': edges,
            'scope': 'Direct finite graph check; not a Lean kernel theorem.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cnf', type=Path, required=True)
    parser.add_argument('--model', type=Path, required=True)
    parser.add_argument('--profile', type=int, required=True)
    parser.add_argument('--cnf-sha256', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('Output must be new')
    try:
        result = verify_candidate(args.cnf, args.model, args.profile, args.cnf_sha256)
    except GraphDecodeError as error:
        with args.output.open('x') as destination:
            json.dump(error.evidence, destination, indent=2)
            destination.write('\n')
        raise SystemExit(str(error))
    with args.output.open('x') as destination:
        json.dump(result, destination, indent=2)
        destination.write('\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'edge_list'}))


if __name__ == '__main__':
    main()
