#!/usr/bin/env python3
"""Offline author-side graph verification; never an independent review receipt."""
import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def decode(directory):
    directory = Path(directory)
    names = ['result.json', 'input.cnf', 'generator-metadata.json', 'solver.log']
    data = {name: (directory / name).read_bytes() for name in names}
    result = json.loads(data['result.json'])
    meta = json.loads(data['generator-metadata.json'])
    require(result['status'] not in {'PREPARED', 'RUNNING'}, 'wait for terminal output')
    for name, field in [('input.cnf', 'cnf'), ('generator-metadata.json', 'metadata'), ('solver.log', 'output')]:
        require(digest(data[name]) == result[field]['sha256'], 'terminal pin mismatch: ' + name)
    n, m, d = meta['n'], meta['m'], meta['minimum_degree']
    require((n, m, d) == (result['n'], result['m'], result['d']), 'run/map parameters differ')
    require(meta['schema'] == 1 and meta['vertex_label'] == 'block*m+residue', 'unsupported map')
    require(n > 0 and m > 0 and n % m == 0, 'invalid action order')
    require(meta['cnf_sha256'] == digest(data['input.cnf']), 'CNF/map binding')
    values = {}
    saw_sat = False
    for line in data['solver.log'].decode().splitlines():
        saw_sat |= line.strip() == 's SATISFIABLE'
        if line.startswith('v '):
            for literal in map(int, line.split()[1:]):
                if literal:
                    var, truth = abs(literal), literal > 0
                    require(var not in values or values[var] == truth, 'conflicting assignment')
                    values[var] = truth
    require(saw_sat, 'no SAT output')
    header = None
    clause = []
    clauses = 0
    for line in data['input.cnf'].decode().splitlines():
        line = line.strip()
        if not line or line.startswith('c'):
            continue
        if line.startswith('p '):
            fields = line.split()
            require(header is None and len(fields) == 4 and fields[:2] == ['p', 'cnf'], 'invalid header')
            header = tuple(map(int, fields[2:]))
            continue
        require(header is not None, 'clause before header')
        for literal in map(int, line.split()):
            if literal:
                require(1 <= abs(literal) <= header[0], 'literal out of range')
                clause.append(literal)
            else:
                require(any(values.get(abs(x)) == (x > 0) for x in clause), 'unsatisfied clause')
                clauses += 1
                clause = []
    require(header == (meta['variables'], meta['clauses']), 'header/map counts differ')
    require(not clause and clauses == header[1], 'clause count or terminator')
    require(set(values) == set(range(1, header[0] + 1)), 'incomplete model')
    translate = lambda v: (v // m) * m + (v % m + 1) % m
    all_pairs, variables, edges = set(), set(), set()
    for orbit in meta['orbits']:
        var = orbit['var']
        require(var in values and var not in variables, 'invalid/duplicate orbit variable')
        variables.add(var)
        pairs = set()
        for pair in orbit['edges']:
            require(len(pair) == 2, 'malformed edge')
            u, v = pair
            require(type(u) is int and type(v) is int and 0 <= u < v < n, 'non-simple edge')
            require((u, v) not in pairs and (u, v) not in all_pairs, 'repeated pair')
            pairs.add((u, v))
        require(pairs, 'empty orbit')
        u, v = next(iter(pairs))
        actual_orbit = set()
        for _ in range(m):
            actual_orbit.add(tuple(sorted((u, v))))
            u, v = translate(u), translate(v)
        require(pairs == actual_orbit, 'map is not one translation orbit')
        all_pairs.update(pairs)
        if values[var]:
            edges.update(pairs)
    require(all_pairs == set(itertools.combinations(range(n), 2)), 'incomplete pair partition')
    adjacency = [set() for _ in range(n)]
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    degrees = list(map(len, adjacency))
    require(min(degrees) >= d, 'minimum degree too small')
    if n == 63 and d == 8:
        require(set(degrees) == {8}, 'N63 calibration must be 8-regular')
    for u, v in itertools.combinations(range(n), 2):
        require(len(adjacency[u] & adjacency[v]) <= 1, 'C4 found')
    require({tuple(sorted((translate(u), translate(v)))) for u, v in edges} == edges, 'action not an automorphism')
    graph = dict(n=n, m=m, minimum_degree=min(degrees), maximum_degree=max(degrees),
                 edges=[list(e) for e in sorted(edges)], adjacency=[sorted(a) for a in adjacency])
    receipt = dict(status='PASS', scope='Author-side CNF and graph check; independent review still required',
                   run_id=result['id'], terminal_status=result['status'], n=n, m=m,
                   required_minimum_degree=d, edges=len(edges), degree_distribution=dict(Counter(degrees)),
                   cnf_variables=header[0], cnf_clauses=clauses,
                   input_sha256={name: digest(raw) for name, raw in data.items()},
                   verifier_sha256=digest(Path(__file__).read_bytes()))
    return graph, receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('run_directory', type=Path)
    parser.add_argument('output_directory', type=Path)
    args = parser.parse_args()
    graph, receipt = decode(args.run_directory)
    args.output_directory.mkdir(parents=True, exist_ok=False)
    raw = (json.dumps(graph, indent=2) + '\n').encode()
    (args.output_directory / 'graph.json').write_bytes(raw)
    receipt['graph_sha256'] = digest(raw)
    (args.output_directory / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
