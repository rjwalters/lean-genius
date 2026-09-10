#!/usr/bin/env python3
"""Check a retained dispatcher SAT candidate without launching a solver."""
import argparse
import hashlib
import json
from pathlib import Path
import re

import verify_h1_sat_graph as h1
import verify_small_high_sat_graph as small


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def file_hash(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()


def select_profile(sector, row):
    if sector == 'H1':
        value = row['profile']
        if type(value) is bool or str(value) not in {'0', '1', '2', '3', '4'}:
            raise ValueError('Invalid H1 profile')
        return int(value)
    if sector == 'H3':
        match = re.fullmatch(r'h3_t([01])_canonical', row['id'])
    elif sector == 'H5':
        match = re.fullmatch(r'h5_t([012])', row['cell'])
    elif sector == 'H7':
        return 0
    else:
        raise ValueError('Unsupported sector')
    if not match:
        raise ValueError('Unrecognized canonical profile')
    return int(match[1])


def check(case_dir, index_path, index_sha256, solver):
    captured = {}

    def read(path):
        path = Path(path)
        if path.stat().st_size > 16*1024*1024:
            raise ValueError('Receipt or manifest exceeds 16 MiB')
        raw = path.read_bytes()
        captured[path] = raw
        return json.loads(raw)

    index = read(index_path)
    if digest(captured[index_path]) != index_sha256:
        raise ValueError('Index hash mismatch')
    result = read(case_dir/'result.json')
    prepared = read(case_dir/'preparation.json')
    name, sector = result['id'], result['sector']
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,159}', name):
        raise ValueError('Invalid case ID')
    solved = read(case_dir/'solve'/name/'result.json')
    if result['status'] not in {'SAT_CANDIDATE', 'DISAGREEMENT'}:
        raise ValueError('Case is not a retained SAT candidate/disagreement')
    if result['index_sha256'] != index_sha256 or result['preparation'] != prepared or result['solve'] != solved:
        raise ValueError('Combined and individual receipts disagree')
    if solved['status'] != result['status'] or any(x['id'] != name or x['sector'] != sector for x in (prepared, solved)):
        raise ValueError('Case identity/status mismatch')
    entries = [r for r in index['cases'] if r['id'] == name]
    if len(entries) != 1 or entries[0]['sector'] != sector:
        raise ValueError('Index case is absent, ambiguous or in another sector')
    source = index['sources'][sector]
    source_path = index_path.parent/source['path']
    manifest = read(source_path)
    if digest(captured[source_path]) != source['sha256'] or prepared['manifest_sha256'] != source['sha256']:
        raise ValueError('Source manifest hash mismatch')
    row = manifest[source['array']][entries[0]['source_index']]
    if row['id'] != name:
        raise ValueError('Source row identity mismatch')
    profile = select_profile(sector, row)
    cnf = Path(prepared['cnf_path'])
    expected = prepared['cnf_sha256']
    if not re.fullmatch(r'[0-9a-f]{64}', expected):
        raise ValueError('Invalid CNF digest')
    if any(x['cnf_sha256'] != expected for x in (result, solved)):
        raise ValueError('Receipt CNF hashes disagree')
    if entries[0]['cnf_sha256'] not in (None, expected):
        raise ValueError('CNF differs from index')
    historical = {v for k, v in row.items() if k.endswith('cnf_sha256') and v}
    if historical and historical != {expected}:
        raise ValueError('CNF differs from source identity')
    record = solved['primary' if solver == 'kissat' else 'crosscheck']
    if record['verdict'] != 'SAT_CANDIDATE' or record['returncode'] != 10 or record['stop_reason'] is not None:
        raise ValueError('Selected solver did not return a complete SAT candidate')
    model = case_dir/'solve'/name/(solver+'.log')
    if model.stat().st_size > 4*1024*1024 or model.stat().st_size != record['log_bytes'] or file_hash(model) != record['log_sha256']:
        raise ValueError('Solver log size/hash mismatch')
    if cnf.stat().st_size > 99_000_000 or file_hash(cnf) != expected:
        raise ValueError('Retained CNF size/hash mismatch')
    try:
        graph = (h1.verify_candidate(cnf, model, profile, expected) if sector == 'H1'
                 else small.verify_candidate(cnf, model, int(sector[1:]), profile, expected))
        if graph['cnf_sha256'] != expected or graph['model_sha256'] != record['log_sha256']:
            raise ValueError('Decoder consumed different input bytes')
    except (h1.GraphDecodeError, small.GraphDecodeError) as error:
        graph = error.evidence
    for path, raw in captured.items():
        if path.read_bytes() != raw:
            raise ValueError('Receipt or manifest changed during verification')
    if file_hash(cnf) != expected or file_hash(model) != record['log_sha256']:
        raise ValueError('Candidate input changed during verification')
    return {'schema': 'erdos85-retained-sat-check-v1', 'id': name, 'sector': sector,
            'profile': profile, 'solver': solver, 'original_solver_status': result['status'],
            'status': graph['status'], 'graph_check': graph,
            'receipt_hashes': {str(p): digest(raw) for p, raw in captured.items()},
            'checker_sha256': file_hash(Path(__file__)),
            'solver_launched': False, 'scope': 'Direct finite graph verification only; rejection is never UNSAT. Original solver receipts remain unchanged.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--case-dir', type=Path, required=True)
    ap.add_argument('--index', type=Path, required=True)
    ap.add_argument('--index-sha256', required=True)
    ap.add_argument('--solver', choices=('kissat', 'cadical'), required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    # Reserve the new output first; never overwrite solver evidence.
    with a.output.open('x') as stream:
        try:
            result = check(a.case_dir, a.index, a.index_sha256, a.solver)
        except (OSError, ValueError, KeyError, IndexError, TypeError) as error:
            result = {'status': 'CANDIDATE_CHECK_ERROR', 'error': str(error),
                      'solver_launched': False, 'scope': 'No graph witness established; never an UNSAT inference.'}
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'status': result['status'], 'output': str(a.output)}))
    return 0 if result['status'] == 'GRAPH_WITNESS_VERIFIED' else 1


if __name__ == '__main__':
    raise SystemExit(main())
