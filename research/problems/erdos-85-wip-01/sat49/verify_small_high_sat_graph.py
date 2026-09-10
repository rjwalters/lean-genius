#!/usr/bin/env python3
"""Check a complete H3/H5/H7 SAT model and its actual order-49 graph."""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path

import verify_dimacs_model as models

SYSTEMS = {3: ((), ((0, 1, 2),)),
           5: ((), ((0, 1, 2),), ((0, 1, 2), (0, 3, 4))),
           7: ((),)}
VARIABLES = {3: 29500, 5: 29632, 7: 17633}


class GraphDecodeError(ValueError):
    def __init__(self, message, evidence):
        super().__init__(message)
        self.evidence = dict(evidence, status='GRAPH_REJECTED', error=message)


def supports(high_count, profile):
    if high_count not in SYSTEMS or not 0 <= profile < len(SYSTEMS[high_count]):
        raise ValueError('Unsupported canonical high-count/profile')
    if high_count == 7:
        return {**{v: set() for v in range(7, 14)},
                **{14 + 2*i + copy: {i} for i in range(7) for copy in range(2)},
                **{28 + i: set(pair) for i, pair in enumerate(itertools.combinations(range(7), 2))}}
    triples = SYSTEMS[high_count][profile]
    covered = {pair for triple in triples for pair in itertools.combinations(triple, 2)}
    rows = [set(t) for t in triples]
    rows += [set(pair) for pair in itertools.combinations(range(high_count), 2) if pair not in covered]
    for point in range(high_count):
        rows += [{point} for _ in range(9-high_count+sum(point in t for t in triples))]
    rows += [set() for _ in range(49-high_count-len(rows))]
    if len(rows) != 49-high_count:
        raise ValueError('Support census exceeds order49')
    return dict(zip(range(high_count, 49), rows, strict=True))


def edge_variables(high_count):
    if high_count == 7:
        edges = list(itertools.combinations(range(7, 49), 2))
        offset = 0
    elif high_count in (3, 5):
        # H3 Python and H5 Lean freight use different high-edge numbering.
        # Their low/low variables share this offset and lexicographic order.
        offset = high_count*(high_count-1)//2 + high_count*(49-high_count)
        edges = list(itertools.combinations(range(high_count, 49), 2))
    else:
        raise ValueError('Unsupported high count')
    return {edge: offset+i+1 for i, edge in enumerate(edges)}


def graph_statistics(order, edges):
    adjacency = [0]*order
    seen = set()
    for a, b in edges:
        if not 0 <= a < b < order or (a, b) in seen:
            raise ValueError('Graph has invalid or duplicate edge')
        seen.add((a, b))
        adjacency[a] |= 1 << b
        adjacency[b] |= 1 << a
    common_max = 0
    witness = None
    for a, b in itertools.combinations(range(order), 2):
        common = adjacency[a] & adjacency[b]
        count = common.bit_count()
        common_max = max(common_max, count)
        if count > 1 and witness is None:
            witnesses = [v for v in range(order) if common >> v & 1][:2]
            witness = {'endpoints': [a, b], 'common_neighbors': witnesses}
    stats = {'order': order, 'edges': len(seen),
             'degrees': [x.bit_count() for x in adjacency],
             'common_neighbor_maximum': common_max, 'c4_free': witness is None}
    if witness is not None:
        raise GraphDecodeError(f'C4 witnessed by {witness}',
                               {'graph': dict(stats, edge_list=[list(e) for e in sorted(seen)],
                                              c4_witness=witness)})
    return adjacency, stats


def decode_and_check(assignment, high_count, profile):
    template = supports(high_count, profile)
    variables = edge_variables(high_count)
    if len(assignment) <= max(variables.values()) or any(
            type(assignment[i]) is not bool for i in variables.values()):
        raise ValueError('Missing or non-Boolean edge assignments')
    edges = {edge for edge, variable in variables.items() if assignment[variable]}
    edges.update((h, low) for low, row in template.items() for h in row)
    adjacency, stats = graph_statistics(49, sorted(edges))
    graph = dict(stats, edge_list=[list(e) for e in sorted(edges)], high_count=high_count,
                 profile=profile, support_counts=dict(Counter(map(len, template.values()))))
    if stats['degrees'] != [8]*high_count + [7]*(49-high_count):
        raise GraphDecodeError('Decoded graph does not have the required49 vertex degrees', {'graph': graph})
    if any(adjacency[h] & ((1 << high_count)-1) for h in range(high_count)):
        raise GraphDecodeError('High vertices are not independent', {'graph': graph})
    return graph


def verify_candidate(cnf, model, high_count, profile, expected_cnf_sha256):
    supports(high_count, profile)  # Validate profile before reading inputs.
    if Path(cnf).stat().st_size > 99_000_000 or Path(model).stat().st_size > 4*1024*1024:
        raise ValueError('Candidate input exceeds retained input/log size bounds')
    # Bound model indices before the generic reader allocates its assignment array.
    with Path(model).open('rb') as source:
        for raw in source:
            fields = raw.split()
            if fields[:1] == [b'v'] and any(abs(int(x)) > VARIABLES[high_count] for x in fields[1:]):
                raise ValueError('Model variable exceeds this canonical encoding')
    variables, clauses, cnf_sha, model_sha = models.verify(Path(cnf), Path(model))
    if variables != VARIABLES[high_count] or cnf_sha != expected_cnf_sha256:
        raise ValueError('CNF encoding/hash differs from the selected input')
    assignment, reread_sha = models.read_model(Path(model))
    if reread_sha != model_sha:
        raise ValueError('Model changed between clause verification and graph decoding')
    try:
        graph = decode_and_check(assignment, high_count, profile)
    except GraphDecodeError as error:
        error.evidence.update(schema='erdos85-small-high-sat-graph-v1',
                              cnf_sha256=cnf_sha, model_sha256=model_sha,
                              cnf_variables=variables, cnf_clauses=clauses,
                              high_count=high_count, profile=profile)
        raise
    return {'schema': 'erdos85-small-high-sat-graph-v1', 'status': 'GRAPH_WITNESS_VERIFIED',
            'cnf_sha256': cnf_sha, 'model_sha256': model_sha,
            'cnf_variables': variables, 'cnf_clauses': clauses, 'graph': graph,
            'decoder_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'model_verifier_sha256': hashlib.sha256(Path(models.__file__).read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cnf', type=Path)
    parser.add_argument('model', type=Path)
    parser.add_argument('--high-count', type=int, choices=(3, 5, 7), required=True)
    parser.add_argument('--profile', type=int, required=True)
    parser.add_argument('--cnf-sha256', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    returncode = 0
    try:
        result = verify_candidate(args.cnf, args.model, args.high_count, args.profile, args.cnf_sha256)
    except GraphDecodeError as error:
        result = error.evidence
        returncode = 1
    with args.output.open('x') as target:
        json.dump(result, target, indent=2)
        target.write('\n')
    print(json.dumps(result))
    return returncode


if __name__ == '__main__':
    raise SystemExit(main())
