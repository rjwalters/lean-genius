#!/usr/bin/env python3
"""Serialized, durable host-only q9 runs. No proof output; no automatic retry."""
import argparse
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
KISSAT = Path('/opt/homebrew/bin/kissat').resolve()
BUDGET = 48 * 3600


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def utc():
    return datetime.now(timezone.utc).isoformat()


def save(path, obj):
    tmp = path.with_suffix('.tmp')
    with tmp.open('w') as f:
        json.dump(obj, f, indent=2, sort_keys=True)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def pin(path):
    path = Path(path).resolve(strict=True)
    return {'path': str(path), 'sha256': sha(path)}


def verify_pin(p):
    if sha(p['path']) != p['sha256']:
        raise ValueError('changed pinned artifact: ' + p['path'])


def scope(n, d, m):
    if (n, d, m) in [(48, 7, 24), (63, 8, 63), (63, 8, 21)]:
        return 'control'
    if d == 9 and ((n == 80 and m in [40, 20, 16, 10, 8, 5, 4, 2]) or
                   (n in [78, 79] and m > 1 and n % m == 0)):
        return 'q9'
    raise ValueError('outside board39 scope')


def policy(ledger, n, d, m, cnf_hash, seed, retry, metadata_hash=None):
    kind = scope(n, d, m)
    runs = ledger['runs']
    if any(r['status'] in ['PREPARED', 'RUNNING'] for r in runs):
        raise ValueError('unfinished run: inspect its existing process; never restart from timeout')
    if any(r['kind'] == 'q9' and (r['status'] == 'SAT' or r.get('sat_observed')) for r in runs):
        raise ValueError('q9 SAT stop rule reached; independently verify the saved witness')
    previous = [r for r in runs if (r['n'], r['d'], r['m']) == (n, d, m)]
    if retry:
        if len(previous) != 1 or previous[0]['status'] != 'UNKNOWN':
            raise ValueError('requeue requires exactly one terminal UNKNOWN initial attempt')
        if previous[0]['cnf']['sha256'] != cnf_hash or previous[0]['seed'] != seed:
            raise ValueError('requeue must retain exact input and seed')
        if metadata_hash is None or previous[0]['metadata']['sha256'] != metadata_hash:
            raise ValueError('requeue must retain exact generator metadata/variable map')
    elif previous:
        raise ValueError('class already attempted; only the authorized UNKNOWN requeue is allowed')
    if kind == 'q9':
        for ncontrol in [48, 63]:
            receipt = ledger['controls'].get(str(ncontrol))
            if not receipt:
                raise ValueError('both independently verified positive controls required')
            verify_pin(receipt['receipt'])
            for p in receipt['artifacts']:
                verify_pin(p)
    spent = sum(r['wall_seconds'] for r in runs)
    # Leave enough room for termination/reaping rather than overrun the budget.
    cap = min(14400 if retry else 3600, math.floor(BUDGET - spent - 5))
    if cap < 1:
        raise ValueError('48 aggregate host-hour budget exhausted')
    return kind, cap


def parse_output(path, exit_code):
    verdicts = []
    with open(path) as f:
        for line in f:
            if line.startswith('s '):
                verdicts.append(line.strip())
    if exit_code == 10 and verdicts == ['s SATISFIABLE']:
        return 'SAT'
    if exit_code == 20 and verdicts == ['s UNSATISFIABLE']:
        return 'UNSAT'
    if exit_code == 0 and (not verdicts or verdicts == ['s UNKNOWN']):
        return 'UNKNOWN'
    return 'ERROR'


def observed_sat(path):
    if not path.exists():
        return False
    with path.open() as f:
        return any(line.strip() == 's SATISFIABLE' for line in f)


def check_model(cnf, log):
    """Directly validate the complete printed assignment against every CNF clause."""
    values = {}
    with open(log) as f:
        for line in f:
            if line.startswith('v '):
                for lit in map(int, line.split()[1:]):
                    if lit:
                        old = values.setdefault(abs(lit), lit > 0)
                        if old != (lit > 0):
                            raise ValueError('conflicting assignment')
    nv = nc = None
    count = 0
    clause = []
    with open(cnf) as f:
        for line in f:
            if not line.strip() or line.startswith('c'):
                continue
            if line.startswith('p '):
                p, fmt, nv, nc = line.split()
                if fmt != 'cnf':
                    raise ValueError('not DIMACS CNF')
                nv, nc = int(nv), int(nc)
                continue
            for lit in map(int, line.split()):
                if lit:
                    clause.append(lit)
                else:
                    if not any(values.get(abs(x)) == (x > 0) for x in clause):
                        raise ValueError('unsatisfied clause ' + str(count))
                    count += 1
                    clause = []
    if clause or count != nc or nv is None or set(values) != set(range(1, nv + 1)):
        raise ValueError('malformed CNF or incomplete assignment')
    return {'variables': nv, 'clauses': count, 'status': 'PASS'}


def run(args, ledger, ledger_path):
    cnf = pin(args.cnf)
    if not cnf['path'].endswith('.cnf'):
        raise ValueError('plain .cnf input required for direct assignment checking')
    metadata = pin(args.metadata)
    kind, cap = policy(ledger, args.n, args.d, args.m, cnf['sha256'], args.seed, args.retry, metadata['sha256'])
    idx = len(ledger['runs'])
    out = ROOT / 'runs' / ('%03d-N%d-m%d' % (idx, args.n, args.m))
    out.mkdir(parents=True, exist_ok=False)
    # Snapshot both input and generator metadata; the solver never reads a mutable source.
    import shutil
    shutil.copyfile(cnf['path'], out / 'input.cnf')
    if sha(out / 'input.cnf') != cnf['sha256']:
        raise ValueError('input changed during snapshot')
    shutil.copyfile(metadata['path'], out / 'generator-metadata.json')
    if sha(out / 'generator-metadata.json') != metadata['sha256']:
        raise ValueError('metadata changed during snapshot')
    command = [str(KISSAT), '--sat', '--strict', '--no-color',
               '--seed=' + str(args.seed), '--time=' + str(cap), str(out / 'input.cnf')]
    r = dict(id=idx, n=args.n, d=args.d, m=args.m, kind=kind, seed=args.seed,
             retry=args.retry, cap_seconds=cap, cnf=cnf, metadata=metadata,
             solver=pin(KISSAT), runner=pin(__file__), command=command,
             solver_version=subprocess.check_output([str(KISSAT), '--version'], text=True).strip(),
             proof_logging=False, status='PREPARED', sat_observed=False, wall_seconds=0,
             prepared_utc=utc(), directory=str(out))
    ledger['runs'].append(r)
    save(ledger_path, ledger)
    process = None
    started = time.monotonic()
    interrupted = None
    def stop(signum, frame):
        raise KeyboardInterrupt('signal ' + str(signum))
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        with (out / 'solver.log').open('w') as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            r.update(status='RUNNING', pid=process.pid, pgid=process.pid,
                     started_utc=utc(), monotonic_start=started)
            save(ledger_path, ledger)
            try:
                process.wait(timeout=cap)
            except subprocess.TimeoutExpired:
                interrupted = 'wall cap'
            except KeyboardInterrupt as exc:
                interrupted = str(exc)
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
        r.update(exit_code=process.returncode,
                 status='UNKNOWN' if interrupted else parse_output(out / 'solver.log', process.returncode))
        if interrupted:
            r['termination_reason'] = interrupted
    except Exception as exc:
        r.update(status='ERROR', error=repr(exc))
        if process is not None and process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
    finally:
        r.update(wall_seconds=time.monotonic() - started, ended_utc=utc(),
                 sat_observed=observed_sat(out / 'solver.log'))
        save(ledger_path, ledger)
    if (out / 'solver.log').exists():
        r['output'] = pin(out / 'solver.log')
    if r['sat_observed']:
        try:
            r['model_check'] = check_model(out / 'input.cnf', out / 'solver.log')
        except Exception as exc:
            # Keep SAT stop flag even if direct validation fails: investigate, do not continue.
            r['model_check'] = {'status': 'FAIL', 'error': repr(exc)}
    save(ledger_path, ledger)
    save(out / 'result.json', r)
    print(json.dumps(r, indent=2))


def register(args, ledger, ledger_path):
    receipt = json.loads(Path(args.receipt).read_text())
    r = ledger['runs'][receipt['run_id']]
    if r['kind'] != 'control' or r['status'] != 'SAT' or r.get('model_check', {}).get('status') != 'PASS':
        raise ValueError('control requires a SAT run with a valid complete CNF assignment')
    if receipt['status'] != 'PASS' or receipt['reviewer'] == 'codex-sol-3':
        raise ValueError('a second seat must independently validate the graph')
    if (receipt['n'], receipt['d'], receipt['m']) != (r['n'], r['d'], r['m']):
        raise ValueError('control parameters disagree')
    if receipt['solver_output_sha256'] != r['output']['sha256']:
        raise ValueError('review does not bind exact solver output')
    artifacts = [receipt[k] for k in ['graph', 'verifier', 'verification_output']]
    for p in artifacts:
        verify_pin(p)
    ledger['controls'][str(r['n'])] = {'run_id': r['id'], 'receipt': pin(args.receipt), 'artifacts': artifacts}
    save(ledger_path, ledger)
    print('registered independently verified control', r['n'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    p = sub.add_parser('run')
    for name in ['n', 'd', 'm']:
        p.add_argument('--' + name, type=int, required=True)
    p.add_argument('--cnf', required=True)
    p.add_argument('--metadata', required=True)
    p.add_argument('--seed', type=int, default=0)
    p.add_argument('--retry', action='store_true')
    p = sub.add_parser('register-control')
    p.add_argument('receipt')
    sub.add_parser('status')
    args = parser.parse_args()
    ROOT.mkdir(exist_ok=True)
    path = ROOT / 'ledger.json'
    with (ROOT / 'runner.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        ledger = json.loads(path.read_text()) if path.exists() else {'runs': [], 'controls': {}}
        if args.action == 'run':
            if args.seed < 0:
                raise ValueError('seed must be nonnegative')
            run(args, ledger, path)
        elif args.action == 'register-control':
            register(args, ledger, path)
        else:
            print(json.dumps(ledger, indent=2))


if __name__ == '__main__':
    main()
