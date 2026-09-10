#!/usr/bin/env python3
"""Reconcile Phase B receipts and logs; never launch or infer a missing solve."""
import argparse
from collections import Counter
import csv
import hashlib
import itertools
import json
from pathlib import Path
import re

from reviewed_historical_snapshot import load_reviewed_history, attach_history

SHA = re.compile(r'[0-9a-f]{64}')
ID = re.compile(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,159}')
SECTORS = {'H1', 'H3', 'H5', 'H7'}
UNSAT = {'UNSAT_PRIMARY', 'UNSAT_CROSSCHECKED'}
STATES = UNSAT | {'UNKNOWN', 'ERROR', 'SAT_CANDIDATE', 'DISAGREEMENT'}
TOOLS = {'dispatch_verdict_only.py', 'run_verdict_only.py',
         'materialize_verdict_input.py', 'materialize_h1_verdict_input.py'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read_bytes(path, limit=32*1024*1024):
    with Path(path).open('rb') as source:
        raw = source.read(limit+1)
    require(len(raw) <= limit, f'Oversize evidence: {path}')
    return raw


def read_json(path, expected=None):
    raw = read_bytes(path)
    require(expected is None or digest(raw) == expected, f'Hash mismatch: {path}')
    return json.loads(raw), raw


def load_index(path, expected):
    index, raw = read_json(path, expected)
    require(index.get('schema') == 'erdos85-phase-b-combined-inventory-v1', 'Wrong index schema')
    require(set(index['sources']) == SECTORS and set(index['counts']) == SECTORS, 'Wrong sectors')
    sources, cases, joins = {}, {}, set()
    for sector, pin in index['sources'].items():
        data, source_raw = read_json(path.parent/pin['path'], pin['sha256'])
        rows = data[pin['array']]
        require(len(rows) == pin['count'] == index['counts'][sector], 'Sector count mismatch')
        sources[sector] = {'data': data, 'rows': rows, 'sha256': digest(source_raw)}
    for entry in index['cases']:
        name, sector, offset = entry['id'], entry['sector'], entry['source_index']
        require(isinstance(name, str) and ID.fullmatch(name) and name not in cases, 'Bad/duplicate case ID')
        require(sector in sources and type(offset) is int and 0 <= offset < len(sources[sector]['rows']), 'Bad source offset')
        require((sector, offset) not in joins, 'Duplicate source join')
        row = sources[sector]['rows'][offset]
        require(row['id'] == name and row.get('cnf_sha256') == entry['cnf_sha256'], 'Index/source mismatch')
        cases[name] = dict(entry, row=row)
        joins.add((sector, offset))
    require(len(cases) == index['total'] == sum(index['counts'].values()), 'Incomplete index')
    return index, raw, sources, cases


def historical_hash(case):
    if case['sector'] != 'H1':
        return case['cnf_sha256']
    values = {v for k, v in case['row'].items() if k.endswith('cnf_sha256') and v}
    require(len(values) <= 1 and all(isinstance(v, str) and SHA.fullmatch(v) for v in values), 'Conflicting H1 input hashes')
    return next(iter(values), None)


def check_preparation(case, prepared, directory, source, config):
    name, sector = case['id'], case['sector']
    require(prepared['id'] == name and prepared['sector'] == sector, 'Preparation case mismatch')
    require(prepared['manifest_sha256'] == source['sha256'], 'Preparation source mismatch')
    actual = prepared['cnf_sha256']
    require(isinstance(actual, str) and SHA.fullmatch(actual), 'Invalid prepared CNF hash')
    expected = historical_hash(case)
    require(expected is None or actual == expected, 'Prepared CNF differs from pinned identity')
    if sector == 'H1':
        require(prepared['identity_basis'] == ('historical' if expected else 'new'), 'Wrong H1 identity basis')
        helper, _ = read_json(directory/'input/receipt.json')
        require(all(prepared.get(k) == v for k, v in helper.items()), 'H1 helper/preparation mismatch')
        require(helper['status'] == 'materialized' and helper['container_absent'] is True, 'Incomplete H1 preparation')
        require(helper.get('emit', {}).get('returncode') == 0, 'H1 emitter did not succeed')
        require(helper['expected_historical_sha256'] == expected, 'H1 historical identity mismatch')
        require(helper['runner_sha256'] == config['tool_sha256']['materialize_h1_verdict_input.py'], 'H1 runner identity mismatch')
        require(helper['validator_sha256'] == config['tool_sha256']['materialize_verdict_input.py'], 'H1 validator identity mismatch')
        row = case['row']
        require(helper['tag'] == row['tag'] and helper['profile'] == int(row['profile']), 'H1 profile/tag mismatch')
        pairs = [(a, b) for a, b in itertools.combinations(range(8), 2) if b != (a ^ 1)]
        table = [(pair, n) for pair, n in zip(pairs, row['table_values'], strict=True) if n]
        require(helper['table_sha256'] == digest((json.dumps(table)+'\n').encode()), 'H1 table mismatch')
        check_log = read_bytes(directory/'input/check.log', 4096).decode('ascii').strip()
        require(helper['check']['returncode'] == 0 and check_log ==
                f"MATCH ({helper['clauses']} clauses, top {helper['variables']})", 'H1 MATCH evidence mismatch')
        require(prepared['generator_commit'] == config['h1_generator_commit'], 'H1 generator provenance mismatch')
    else:
        data, row = source['data'], case['row']
        if sector == 'H3':
            require(prepared['status'] == 'validated_existing' and prepared['generated'] is False, 'Wrong H3 preparation')
            require((prepared['variables'], prepared['clauses'], prepared['bytes']) ==
                    (row['variables'], row['clauses'], row['bytes']), 'H3 dimensions mismatch')
            generator = row['generator_commit']
        else:
            require(prepared['status'] == 'materialized' and prepared['generated'] is True, 'Incomplete cube preparation')
            require(prepared['units'] == row['units'] and prepared['cnf_bytes'] == row['cnf_bytes'], 'Cube identity mismatch')
            variables = row['variables'] if sector == 'H5' else data['variables']
            clauses = row['clauses'] if sector == 'H5' else data['cube_clauses']
            require((prepared['variables'], prepared['clauses']) == (variables, clauses), 'Cube dimensions mismatch')
            generator = data['generator']['last_change_commit']
        require(prepared['generator_commit'] == generator, 'Generator provenance mismatch')
    return actual


def check_solver(receipt, log_path, kind, prepared, identity, cap):
    raw = read_bytes(log_path, 4*1024*1024)
    require(digest(raw) == receipt['log_sha256'] and len(raw) == receipt['log_bytes'], 'Solver log identity mismatch')
    require(receipt['proof_requested'] is False, 'Proof logging receipt is unsupported')
    require(receipt['solver_sha256'] == identity['sha256'], 'Solver identity differs from invocation')
    options = [f'--time={cap}'] if kind == 'kissat' else ['-t', str(cap)]
    require(receipt['command'] == [identity['path'], *options, prepared['cnf_path']], 'Solver command/input mismatch')
    statuses = [line.strip() for line in raw.splitlines() if line.startswith(b's ')]
    rc = receipt['returncode']
    if receipt['stop_reason'] is not None:
        verdict = 'UNKNOWN'
    elif rc == 20 and statuses == [b's UNSATISFIABLE']:
        verdict = 'UNSAT'
    elif rc == 10 and statuses == [b's SATISFIABLE']:
        verdict = 'SAT_CANDIDATE'
    elif rc == 0 and statuses in ([], [b's UNKNOWN']):
        verdict = 'UNKNOWN'
    else:
        verdict = 'ERROR'
    require(receipt['verdict'] == verdict, 'Solver verdict disagrees with log/exit/cap evidence')
    return verdict


def check_case(record, case, run, source, config, state):
    directory = run/case['id']
    saved, saved_raw = read_json(directory/'result.json')
    require(saved == record, 'Invocation/case receipt mismatch')
    require(record['sector'] == case['sector'] and record['index_sha256'] == state['index_sha256'], 'Case identity mismatch')
    require(record['status'] in STATES, 'Unknown case status')
    evidence = {'run': str(run), 'status': record['status'], 'case_receipt_sha256': digest(saved_raw)}
    if record['status'] == 'ERROR':
        # A later cleanup/provenance error can overwrite the root status after
        # a solver reported SAT. Keep that alarm even though this attempt does
        # not qualify as validated solver evidence.
        child = record.get('solve', {})
        evidence['sat_alarm'] = (child.get('status') in {'SAT_CANDIDATE', 'DISAGREEMENT'} or
                                any(child.get(key, {}).get('verdict') == 'SAT_CANDIDATE'
                                    for key in ('primary', 'crosscheck')))
        return evidence
    prepared, _ = read_json(directory/'preparation.json')
    require(prepared == record['preparation'], 'Combined/preparation receipt mismatch')
    cnf_sha = check_preparation(case, prepared, directory, source, config)
    solved, _ = read_json(directory/'solve'/case['id']/'result.json')
    require(solved == record['solve'], 'Combined/solver receipt mismatch')
    require(solved['id'] == case['id'] and solved['sector'] == case['sector'], 'Solver case mismatch')
    require(solved['cnf_sha256'] == record['cnf_sha256'] == cnf_sha, 'Solver input hash mismatch')
    require(solved['generator_commit'] == prepared['generator_commit'], 'Solver generator mismatch')
    policy = dict(config['policies'][case['sector']])
    if case['id'] in config.get('crosscheck_ids', []):
        policy['crosscheck'] = True
    require(type(policy['crosscheck']) is bool and (case['sector'] == 'H1' or policy['crosscheck']), 'Missing hard-sector cross-check policy')
    solver_dir = directory/'solve'/case['id']
    primary = check_solver(solved['primary'], solver_dir/'kissat.log', 'kissat', prepared,
                           state['solvers']['kissat'], policy['primary_cap_seconds'])
    if primary == 'UNSAT' and policy['crosscheck']:
        secondary = check_solver(solved['crosscheck'], solver_dir/'cadical.log', 'cadical', prepared,
                                 state['solvers']['cadical'], policy['crosscheck_cap_seconds'])
        status = {'UNSAT': 'UNSAT_CROSSCHECKED', 'UNKNOWN': 'UNKNOWN',
                  'SAT_CANDIDATE': 'DISAGREEMENT', 'ERROR': 'ERROR'}[secondary]
    else:
        require('crosscheck' not in solved, 'Unexpected secondary result')
        status = 'UNSAT_PRIMARY' if primary == 'UNSAT' else primary
    require(record['status'] == solved['status'] == status, 'Combined verdict disagrees with solver evidence')
    return dict(evidence, cnf_sha256=cnf_sha)


def retained_partial(run, name):
    """Preserve evidence at every worker publication boundary, never infer UNSAT."""
    directory = run/name
    artifacts, sat_alarm = [], False
    for relative in ('result.json', 'preparation.json', f'solve/{name}/result.json',
                     f'solve/{name}/kissat.log', f'solve/{name}/cadical.log'):
        path = directory/relative
        if not path.exists():
            continue
        raw = read_bytes(path, 4*1024*1024 if path.suffix == '.log' else 32*1024*1024)
        artifacts.append({'path': relative, 'sha256': digest(raw), 'bytes': len(raw)})
        if path.suffix == '.log':
            sat_alarm |= any(line.strip() == b's SATISFIABLE' for line in raw.splitlines())
        else:
            data = json.loads(raw)
            children = [data, data.get('solve', {})]
            sat_alarm |= any(child.get('status') in {'SAT_CANDIDATE', 'DISAGREEMENT'} or
                             any(child.get(key, {}).get('verdict') == 'SAT_CANDIDATE'
                                 for key in ('primary', 'crosscheck')) for child in children)
    return {'run': str(run), 'status': 'INCOMPLETE', 'publication': 'partial_worker_evidence',
            'sat_alarm': sat_alarm, 'artifacts': artifacts}


def combine(attempts, incomplete):
    statuses = {a['status'] for a in attempts}
    hashes = {a['cnf_sha256'] for a in attempts if 'cnf_sha256' in a}
    if (any(a.get('sat_alarm') for a in attempts) or len(hashes) > 1 or
            'DISAGREEMENT' in statuses or ('SAT_CANDIDATE' in statuses and statuses & UNSAT)):
        return 'DISAGREEMENT'
    if 'SAT_CANDIDATE' in statuses:
        return 'SAT_CANDIDATE'
    if incomplete or 'INCOMPLETE' in statuses:
        return 'INCOMPLETE'
    for status in ('UNSAT_CROSSCHECKED', 'UNSAT_PRIMARY', 'UNKNOWN', 'ERROR'):
        if status in statuses:
            return status
    return 'INCOMPLETE' if incomplete else 'NOT_RUN'


def summarize(index_path, index_sha256, run_dirs):
    index_path = Path(index_path).resolve()
    index, index_raw, sources, cases = load_index(index_path, index_sha256)
    attempts = {name: [] for name in cases}
    incomplete = set()
    runs, seen_runs = [], set()
    historical = {}
    for directory in run_dirs:
        run = Path(directory).resolve()
        require(run not in seen_runs, 'Duplicate run directory')
        seen_runs.add(run)
        state, state_raw = read_json(run/'results.json')
        require(state.get('schema') == 'erdos85-dispatch-results-v1', 'Wrong run schema')
        require(state['index_sha256'] == digest(index_raw) and state['inventory_cases'] == len(cases), 'Run/index mismatch')
        require(state['proof_logging'] is False, 'Unsupported proof-producing run')
        snapshots = {}
        for path in (run/'snapshots').iterdir():
            if path.is_file():
                raw = read_bytes(path)
                snapshots[digest(raw)] = raw
        require(state['config_sha256'] in snapshots, 'Missing config snapshot')
        config = json.loads(snapshots[state['config_sha256']])
        require(config['schema'] == 'erdos85-dispatch-v1' and config['index']['sha256'] == index_sha256, 'Config/index mismatch')
        require(set(config['tool_sha256']) in (TOOLS, TOOLS | {'historical_verdict_overlay.py'}) and
                all(isinstance(v, str) and SHA.fullmatch(v) for v in config['tool_sha256'].values()),
                'Invalid tool pins')
        require(set(config['policies']) == SECTORS, 'Invalid policy sectors')
        for sector, policy in config['policies'].items():
            require(type(policy['crosscheck']) is bool and (sector == 'H1' or policy['crosscheck']),
                    'Invalid cross-check policy')
            for key in ('primary_cap_seconds', 'crosscheck_cap_seconds'):
                require(type(policy[key]) is int and 1 <= policy[key] <= 86400, 'Invalid solver cap')
        overrides = config.get('crosscheck_ids', [])
        require(isinstance(overrides, list) and len(set(overrides)) == len(overrides) and
                all(name in cases and cases[name]['sector'] == 'H1' for name in overrides),
                'Invalid cross-check overrides')
        required = {index_sha256, *(s['sha256'] for s in sources.values()), *config['tool_sha256'].values()}
        require(required <= set(snapshots), 'Missing transitive input/tool snapshots')
        selected = state['selected_cases']
        require(len(set(selected)) == len(selected) and set(selected) <= set(cases), 'Invalid selection')
        current_history = load_reviewed_history(config, snapshots, state, cases, sources['H1']['sha256'])
        for name, record in current_history.items():
            require(name not in historical or historical[name] == record, 'Historical evidence differs across runs')
            historical[name] = record
        done = set()
        for record in state['results']:
            name = record['id']
            require(name in selected and name not in done, 'Unexpected/duplicate completed case')
            done.add(name)
            attempt = check_case(record, cases[name], run, sources[cases[name]['sector']], config, state)
            retained = retained_partial(run, name)
            # A capped UNKNOWN may already have emitted SAT. Scan all paths,
            # not just ERROR/partial publication. An ordinary validated SAT
            # candidate keeps its own status; a capped SAT is only an alarm.
            attempt['sat_alarm'] = (attempt.get('sat_alarm', False) or
                                    (record['status'] != 'SAT_CANDIDATE' and retained['sat_alarm']))
            attempt['artifacts'] = retained['artifacts']
            attempts[name].append(attempt)
        missing = set(selected)-done
        if 'not_started' in state:
            require(set(state['not_started']) == missing and len(state['not_started']) == len(missing), 'Incorrect not_started list')
        else:
            incomplete.update(missing)
        for name in missing:
            # A child can publish before the parent receives its Future. Even
            # an earlier valid UNSAT cannot hide this unfinished attempt.
            if (run/name).exists():
                attempts[name].append(retained_partial(run, name))
                incomplete.add(name)
        require(state['status'] != 'complete' or not missing, 'Incomplete run declared complete')
        runs.append({'path': str(run), 'results_sha256': digest(state_raw),
                     'config_sha256': state['config_sha256'], 'recorded_config_commit': state['config_commit'],
                     'selected': len(selected), 'completed': len(done)})
    rows = [{'id': name, 'sector': case['sector'], 'status': combine(attempts[name], name in incomplete),
             'attempts': attempts[name]} for name, case in cases.items()]
    rows = [attach_history(row, historical.get(row['id'])) for row in rows]
    counts = dict(Counter(row['status'] for row in rows))
    return {'schema': 'erdos85-phase-b-verdict-table-v1',
            'scope': 'Receipt/log consistency over the pinned current target index. Historical screened exclusions, graph witnesses, kernel certificates and execution authenticity are not revalidated.',
            'index_sha256': index_sha256, 'historical_evidence_cases': len(historical), 'total': len(rows), 'counts': counts, 'runs': runs, 'rows': rows,
            'all_targets_crosschecked_unsat': bool(rows) and all(r['status'] == 'UNSAT_CROSSCHECKED' for r in rows),
            'has_disagreement': any(r['status'] == 'DISAGREEMENT' for r in rows)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--index', required=True, type=Path)
    parser.add_argument('--index-sha256', required=True)
    parser.add_argument('--run-dir', action='append', default=[], type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--tsv', type=Path)
    args = parser.parse_args()
    result = summarize(args.index, args.index_sha256, args.run_dir)
    with args.output.open('x') as out:
        json.dump(result, out, indent=2)
        out.write('\n')
    if args.tsv:
        with args.tsv.open('x', newline='') as out:
            writer = csv.writer(out, delimiter='\t')
            writer.writerow(['id', 'sector', 'status', 'attempts'])
            writer.writerows((r['id'], r['sector'], r['status'], len(r['attempts'])) for r in result['rows'])
    print(json.dumps({k: v for k, v in result.items() if k not in ('rows', 'runs')}))


if __name__ == '__main__':
    main()
