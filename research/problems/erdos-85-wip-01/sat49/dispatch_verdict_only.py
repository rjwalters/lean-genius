#!/usr/bin/env python3
"""Prepare and solve one Phase B input per worker; dry run unless --execute.

The committed run configuration pins the complete index, transitive manifests,
source tools, caps and launch time. Preparation occupies the same bounded slot
as both solvers. Only newly generated, successfully receipted non-SAT inputs
are removed; existing inputs and every error/SAT input remain intact.
"""
from __future__ import annotations
import argparse
import concurrent.futures as futures
import datetime as dt
import hashlib
import json
from pathlib import Path
import shutil
import os

import run_verdict_only as runner
import materialize_verdict_input as units
import materialize_h1_verdict_input as h1

COUNTS = {'H1': 1257, 'H3': 2, 'H5': 129, 'H7': 28}
TOOLS = ('dispatch_verdict_only.py', 'run_verdict_only.py',
         'materialize_verdict_input.py', 'materialize_h1_verdict_input.py')
UNSAT = {'UNSAT_PRIMARY', 'UNSAT_CROSSCHECKED'}
STOP = {'ERROR', 'SAT_CANDIDATE', 'DISAGREEMENT'}
RESERVE = 8 * 1024**3


def snapshot(path, expected=None):
    raw = path.read_bytes()
    if expected is not None and hashlib.sha256(raw).hexdigest() != expected:
        raise ValueError(f'Pinned bytes changed: {path}')
    return raw, json.loads(raw)


def load_plan(path):
    raw, config = snapshot(path)
    if config.get('schema') != 'erdos85-dispatch-v1':
        raise ValueError('Expected erdos85-dispatch-v1')
    start = dt.datetime.fromisoformat(config['not_before'].replace('Z', '+00:00'))
    if start.tzinfo is None:
        raise ValueError('Launch time requires timezone')
    if type(config['generation_cap_seconds']) is not int or not 1 <= config['generation_cap_seconds'] <= 600:
        raise ValueError('Invalid generation cap')
    if set(config['policies']) != set(COUNTS):
        raise ValueError('Exactly four sector policies required')
    for sector, policy in config['policies'].items():
        if type(policy['crosscheck']) is not bool or (sector != 'H1' and not policy['crosscheck']):
            raise ValueError('Hard sectors require cross-check')
        for key in ('primary_cap_seconds', 'crosscheck_cap_seconds'):
            if type(policy[key]) is not int or not 1 <= policy[key] <= 86400:
                raise ValueError('Invalid solver cap')
    if set(config['tool_sha256']) != set(TOOLS):
        raise ValueError('Exact tool pins required')
    captured = [(path, raw)]
    for name in TOOLS:
        tool = Path(__file__).parent / name
        data = tool.read_bytes()
        if hashlib.sha256(data).hexdigest() != config['tool_sha256'][name]:
            raise ValueError(f'Tool identity mismatch: {name}')
        captured.append((tool, data))
    index_path = (path.parent / config['index']['path']).resolve()
    index_raw, index = snapshot(index_path, config['index']['sha256'])
    captured.append((index_path, index_raw))
    if index.get('schema') != 'erdos85-phase-b-combined-inventory-v1' or index['counts'] != COUNTS or index['total'] != 1416:
        raise ValueError('Expected complete frozen 1416-case index')
    sources = {}
    for sector in COUNTS:
        ref = index['sources'][sector]
        source_path = (index_path.parent / ref['path']).resolve()
        source_raw, data = snapshot(source_path, ref['sha256'])
        captured.append((source_path, source_raw))
        rows = data[ref['array']]
        if len(rows) != COUNTS[sector] or ref['count'] != len(rows):
            raise ValueError('Sector count mismatch')
        sources[sector] = {'path': source_path, 'sha256': ref['sha256'], 'data': data, 'rows': rows}
    overrides = config.get('crosscheck_ids', [])
    if not isinstance(overrides, list) or len(set(overrides)) != len(overrides):
        raise ValueError('Duplicate/invalid crosscheck IDs')
    seen, joins, cases = set(), set(), []
    for entry in index['cases']:
        name, sector, offset = entry['id'], entry['sector'], entry['source_index']
        if not runner.ID.fullmatch(name) or name in seen or sector not in COUNTS:
            raise ValueError('Invalid/duplicate index identity')
        if type(offset) is not int or not 0 <= offset < COUNTS[sector] or (sector, offset) in joins:
            raise ValueError('Invalid/duplicate source join')
        row = sources[sector]['rows'][offset]
        if row['id'] != name or row.get('cnf_sha256') != entry['cnf_sha256']:
            raise ValueError('Index/source identity mismatch')
        seen.add(name); joins.add((sector, offset))
        historical = None
        if sector == 'H1':
            hashes = {value for key, value in row.items() if key.endswith('cnf_sha256') and value}
            if len(hashes) > 1 or any(not runner.HEX.fullmatch(value) for value in hashes):
                raise ValueError('Conflicting/invalid H1 historical hashes')
            historical = next(iter(hashes), None)
        policy = dict(config['policies'][sector])
        if name in overrides:
            if sector != 'H1':
                raise ValueError('Crosscheck overrides are for H1 rows only')
            policy['crosscheck'] = True
        cases.append(dict(entry, row=row, policy=policy, expected_historical_sha256=historical))
    if len(cases) != 1416 or len(joins) != sum(COUNTS.values()):
        raise ValueError('Incomplete source bijection')
    if not set(overrides) <= seen:
        raise ValueError('Unknown crosscheck ID')
    return {'config': config, 'raw': raw, 'index': index, 'sources': sources,
            'captured': captured, 'cases': cases}


def check_sources(plan):
    for path, raw in plan['captured']:
        if path.read_bytes() != raw:
            raise ValueError(f'Captured dependency changed: {path}')


def prepare(case, plan, directory):
    sector = case['sector']; source = plan['sources'][sector]
    if runner.ABORT.is_set():
        raise InterruptedError('Cancelled before input preparation')
    if sector == 'H1':
        result = h1.materialize(source['path'], source['sha256'], case['id'], directory / 'input',
            timeout=plan['config']['generation_cap_seconds'], cancelled=runner.ABORT.is_set)
        expected = case['expected_historical_sha256']
        actual = runner.sha256(Path(result['cnf_path']))
        if actual != result['cnf_sha256'] or (expected is not None and actual != expected):
            raise ValueError('H1 prepared input differs from frozen historical identity')
        result.update(identity_basis='historical' if expected is not None else 'new',
                      expected_historical_sha256=expected)
        # Historical native producer; avoid mislabelling this as a source rebuild.
        generator_commit = plan['config']['h1_generator_commit']
    elif sector in ('H5', 'H7'):
        result = units.materialize_inventory_case(source['path'], source['sha256'],
                                                   case['id'], directory / 'input.cnf')
        generator_commit = source['data']['generator']['last_change_commit']
    else:
        row = case['row']; path = Path(row['cnf_path'])
        stats = units.validate_dimacs(path, expected_variables=row['variables'], expected_clauses=row['clauses'])
        if stats['sha256'] != row['cnf_sha256'] or stats['bytes'] != row['bytes']:
            raise ValueError('Existing H3 input identity mismatch')
        result = dict(stats, id=case['id'], sector=sector, cnf_path=str(path),
                      cnf_sha256=stats['sha256'], status='validated_existing')
        generator_commit = row['generator_commit']
    if not runner.COMMIT.fullmatch(generator_commit):
        raise ValueError('Invalid generator provenance commit')
    if result['id'] != case['id'] or result['sector'] != sector:
        raise ValueError('Prepared identity mismatch')
    if case['cnf_sha256'] is not None and result['cnf_sha256'] != case['cnf_sha256']:
        raise ValueError('Prepared input differs from index')
    result.update(manifest_sha256=source['sha256'], generated=sector != 'H3',
                  generator_commit=generator_commit)
    return result


def run_prepared_case(case, plan, output, kissat, cadical):
    directory = output / case['id']
    result = {'id': case['id'], 'sector': case['sector'], 'status': 'ERROR',
              'index_sha256': plan['config']['index']['sha256']}
    created = False
    try:
        directory.mkdir()
        created = True
        check_sources(plan)
        if shutil.disk_usage(output).free < RESERVE:
            raise OSError('Fewer than 8 GiB free before preparation')
        prepared = prepare(case, plan, directory)
        result['preparation'] = prepared
        runner.write_json(directory / 'preparation.json', prepared)
        check_sources(plan)
        if runner.ABORT.is_set():
            raise InterruptedError('Cancelled after input preparation')
        if shutil.disk_usage(output).free < RESERVE:
            raise OSError('Fewer than 8 GiB free after preparation')
        solving = dict(case['policy'], id=case['id'], sector=case['sector'],
                       resolved_cnf=prepared['cnf_path'], cnf_sha256=prepared['cnf_sha256'],
                       generator_commit=prepared['generator_commit'])
        solve_output = directory / 'solve'; solve_output.mkdir()
        solved = runner.run_case(solving, solve_output, kissat, cadical)
        result.update(status=solved['status'], solve=solved, cnf_sha256=prepared['cnf_sha256'])
        check_sources(plan)
        runner.write_json(directory / 'result.json', result)
        # Remove only a fresh input created inside this exclusive case directory.
        # Keep SAT/error/aborted inputs for inspection, as well as all old bases.
        if prepared['generated'] and result['status'] in UNSAT | {'UNKNOWN'} and not runner.ABORT.is_set():
            path = Path(prepared['cnf_path'])
            if path.is_symlink() or not path.resolve().is_relative_to(directory.resolve()):
                raise ValueError('Refusing cleanup outside owned case directory')
            if runner.sha256(path) != prepared['cnf_sha256']:
                raise ValueError('Input changed before cleanup')
            path.unlink()
            result['generated_input_removed'] = True
    except Exception as error:
        result.update(status='ERROR', error=f'{type(error).__name__}: {error}')
    if created:
        runner.write_json(directory / 'result.json', result)
    return result


def dispatch(cases, worker, workers, output, state):
    results = state['results']; stopped = False
    with futures.ThreadPoolExecutor(max_workers=workers) as pool:
        todo = iter(cases)
        pending = {pool.submit(worker, next(todo)) for _ in range(min(workers, len(cases)))}
        while pending:
            done, pending = futures.wait(pending, return_when=futures.FIRST_COMPLETED)
            batch = [future.result() for future in done]
            results.extend(batch)
            stopped |= any(r['status'] in STOP for r in batch)
            stopped |= runner.ABORT.is_set() or shutil.disk_usage(output).free < RESERVE
            state['status'] = 'aborted' if runner.ABORT.is_set() else 'draining' if stopped else 'running'
            runner.write_json(output / 'results.json', state)
            if not stopped:
                for _ in batch:
                    case = next(todo, None)
                    if case is not None:
                        pending.add(pool.submit(worker, case))
    completed = {r['id'] for r in results}
    state['not_started'] = [c['id'] for c in cases if c['id'] not in completed]
    state['status'] = 'aborted' if runner.ABORT.is_set() else 'stopped' if stopped else 'complete'
    state['selected_all_unsat'] = bool(cases) and not state['not_started'] and all(r['status'] in UNSAT for r in results)
    state['inventory_all_unsat'] = len(cases) == 1416 and state['selected_all_unsat']
    runner.write_json(output / 'results.json', state)
    return state


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--config-commit')
    parser.add_argument('--execute', action='store_true')
    parser.add_argument('--case-id', action='append')
    parser.add_argument('--workers', type=int, choices=range(1, 5), default=1)
    parser.add_argument('--output-dir', type=Path)
    parser.add_argument('--kissat', type=Path, default=Path('/opt/homebrew/bin/kissat'))
    parser.add_argument('--cadical', type=Path, default=Path('/opt/homebrew/bin/cadical'))
    args = parser.parse_args()
    plan = load_plan(args.config.resolve()); config = plan['config']; cases = plan['cases']
    if args.case_id:
        selected = set(args.case_id)
        if len(selected) != len(args.case_id) or not selected <= {c['id'] for c in cases}:
            parser.error('Duplicate or unknown case ID')
        cases = [c for c in cases if c['id'] in selected]
    if not args.execute:
        print(json.dumps({'mode': 'dry_run', 'inventory_cases': 1416, 'selected_cases': len(cases),
                          'not_before': config['not_before'], 'workers': args.workers,
                          'input_preparation': 'per worker; no input generated or solver launched'}))
        return 0
    if not args.config_commit or not args.output_dir:
        parser.error('Execution requires exact config commit and new output directory')
    for path, raw in plan['captured']:
        runner.require_banked_inventory(path, args.config_commit, expected_bytes=raw)
    if dt.datetime.now(dt.timezone.utc) < dt.datetime.fromisoformat(config['not_before'].replace('Z', '+00:00')):
        parser.error('Execution window has not started')
    output = args.output_dir.resolve(); output.parent.mkdir(parents=True, exist_ok=True)
    if shutil.disk_usage(output.parent).free < RESERVE:
        parser.error('Fewer than 8 GiB free')
    output.mkdir()
    retained = output / 'snapshots'; retained.mkdir()
    for number, (path, raw) in enumerate(plan['captured']):
        (retained / f'{number:02d}-{path.name}').write_bytes(raw)
    identities = {name: runner.solver_identity(binary.resolve()) for name, binary in
                  [('kissat', args.kissat), ('cadical', args.cadical)]}
    state = {'schema': 'erdos85-dispatch-results-v1', 'status': 'running', 'pid': os.getpid(),
             'config_sha256': hashlib.sha256(plan['raw']).hexdigest(), 'config_commit': args.config_commit,
             'index_sha256': config['index']['sha256'], 'inventory_cases': 1416,
             'selected_cases': [c['id'] for c in cases], 'workers': args.workers,
             'solvers': identities, 'proof_logging': False, 'results': []}
    runner.write_json(output / 'results.json', state)
    with runner.cancellation_handlers():
        dispatch(cases, lambda c: run_prepared_case(c, plan, output, args.kissat.resolve(), args.cadical.resolve()),
                 args.workers, output, state)
    print(json.dumps({k: v for k, v in state.items() if k not in ('results', 'solvers')}))
    return 0 if state['selected_all_unsat'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
