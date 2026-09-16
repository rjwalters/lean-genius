#!/usr/bin/env python3
"""Materialize one H1 canonical input; never invoke a SAT solver."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import signal
import subprocess
import time
import uuid

import materialize_verdict_input as validator
from materialize_verdict_input import MAX_INPUT_BYTES, validate_dimacs, validate_emitter_match

EMITTER_SHA256 = '4bd9604c6d670ad65a8ca332a26dbf35132418634a3b0678c177c8b2cfff4bf6'
IMAGE_ID = 'sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6'
DEFAULT_EMITTER = Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex/h1fleet/v3freight-rebuild-20260905/stage/freight/v2cnf')
PAIRS = [(c, j) for c in range(8) for j in range(c + 1, 8) if j != (c ^ 1)]
SHA = re.compile(r'[0-9a-f]{64}')


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as source:
        for block in iter(lambda: source.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def select_input(manifest, expected_sha, case_id):
    raw = Path(manifest).read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected_sha:
        raise ValueError('Inventory hash mismatch')
    data = json.loads(raw)
    if data.get('schema') != 'erdos85-phase-b-h1-candidates-v1':
        raise ValueError('Unsupported H1 inventory schema')
    found = [row for row in data['rows'] if row['id'] == case_id]
    if len(found) != 1:
        raise ValueError('Case absent or duplicated')
    row = found[0]
    if str(row['profile']) not in {'0', '1', '2', '3', '4'}:
        raise ValueError('Invalid H1 profile')
    values = row['table_values']
    if len(values) != 24 or any(type(v) is not int or not 0 <= v <= 5 for v in values):
        raise ValueError('Invalid 24-entry miss table')
    table = {pair: v for pair, v in zip(PAIRS, values, strict=True) if v}
    tag = hashlib.sha1(json.dumps(sorted(table.items())).encode()).hexdigest()[:16]
    if row['tag'] != tag or case_id != 'h1_' + tag:
        raise ValueError('Table/tag/case identity mismatch')
    hashes = {row.get(key) for key in ('host_cnf_sha256', 'fleet_cnf_sha256',
              'fleet_v2_cnf_sha256', 'fleet_v3_cnf_sha256') if row.get(key)}
    if len(hashes) > 1 or any(not SHA.fullmatch(x) for x in hashes):
        raise ValueError('Conflicting or malformed historical CNF hashes')
    return row, json.dumps(sorted(table.items())) + '\n', next(iter(hashes), None)


def bounded_process(command, stdout_path, stderr_path, *, stdout_limit, timeout, cancelled=None):
    """Bound captured bytes while draining both streams; stop the client on failure."""
    started = time.monotonic()
    process = None
    sizes = {'stdout': 0, 'stderr': 0}
    with stdout_path.open('xb') as out, stderr_path.open('xb') as err:
        try:
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       start_new_session=True)
            with selectors.DefaultSelector() as poller:
                poller.register(process.stdout, selectors.EVENT_READ, ('stdout', out, stdout_limit))
                poller.register(process.stderr, selectors.EVENT_READ, ('stderr', err, 1024 * 1024))
                while poller.get_map() or process.poll() is None:
                    if cancelled is not None and cancelled():
                        raise InterruptedError('Input stage cancelled')
                    if time.monotonic() - started > timeout:
                        raise TimeoutError('Input stage exceeded wall-time cap')
                    for key, _ in poller.select(0.1):
                        chunk = os.read(key.fileobj.fileno(), 65536)
                        if not chunk:
                            poller.unregister(key.fileobj)
                            key.fileobj.close()
                            continue
                        name, destination, limit = key.data
                        remaining = limit - sizes[name]
                        destination.write(chunk[:remaining])
                        sizes[name] += min(len(chunk), remaining)
                        if len(chunk) > remaining:
                            raise ValueError(f'{name} exceeded byte cap')
                rc = process.wait()
        finally:
            if process is not None:
                # Docker container lifetime is handled separately by its unique name.
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
                for stream in (process.stdout, process.stderr):
                    if stream is not None and not stream.closed:
                        stream.close()
    return {'returncode': rc, 'seconds': time.monotonic() - started,
            'stdout_bytes': sizes['stdout'], 'stderr_bytes': sizes['stderr'], 'command': command}


def materialize(manifest, manifest_sha256, case_id, output_dir, *, emitter=DEFAULT_EMITTER,
                docker='/usr/local/bin/docker', timeout=120, cancelled=None):
    if not 1 <= timeout <= 600:
        raise ValueError('Generation cap must be 1..600 seconds')
    row, table, expected = select_input(manifest, manifest_sha256, case_id)
    emitter = Path(emitter).resolve()
    if sha256(emitter) != EMITTER_SHA256:
        raise ValueError('Emitter identity mismatch')
    identity = subprocess.run([docker, 'image', 'inspect', IMAGE_ID, '--format', '{{.Id}}'],
                              capture_output=True, text=True, timeout=15, check=True).stdout.strip()
    if identity != IMAGE_ID:
        raise ValueError('Installed image identity mismatch')
    output_dir = Path(output_dir).resolve()
    output_dir.mkdir()  # Exclusive owned directory; never overwrite retained inputs.
    result = {'id': case_id, 'sector': 'H1', 'status': 'ERROR',
              'manifest_sha256': manifest_sha256, 'emitter_sha256': EMITTER_SHA256,
              'image_id': IMAGE_ID, 'expected_historical_sha256': expected,
              'receipt_path': str(output_dir / 'receipt.json'),
              'profile': int(row['profile']), 'tag': row['tag'], 'solver_launched': False,
              'runner_sha256': sha256(Path(__file__)),
              'validator_sha256': sha256(Path(validator.__file__))}
    name = 'erdos85-h1-input-' + uuid.uuid4().hex
    cnf = output_dir / 'input.cnf'
    table_path = output_dir / 'table.json'
    table_path.write_text(table)
    result['table_sha256'] = sha256(table_path)
    base = [docker, 'run', '--rm', '--name', name, '--read-only', '--network', 'none',
            '--memory', '8g', '--cpus', '1', '--pids-limit', '64',
            '--mount', f'type=bind,src={emitter},dst=/v2cnf,readonly',
            '--mount', f'type=bind,src={output_dir},dst=/inputs,readonly', IMAGE_ID,
            '/usr/bin/timeout', '--signal=TERM', '--kill-after=5s', str(timeout) + 's', '/v2cnf']
    cleanup = None
    try:
        result['emit'] = bounded_process(base + ['emit', str(row['profile']), '/inputs/table.json'],
            cnf, output_dir / 'emit.err', stdout_limit=MAX_INPUT_BYTES, timeout=timeout, cancelled=cancelled)
        if result['emit']['returncode'] != 0:
            raise ValueError('Emitter failed')
        stats = validate_dimacs(cnf)
        if expected is not None and stats['sha256'] != expected:
            raise ValueError('Emitted CNF differs from historical producer hash')
        result['check'] = bounded_process(base + ['check', str(row['profile']), '/inputs/table.json',
            '/inputs/input.cnf'], output_dir / 'check.log', output_dir / 'check.err',
            stdout_limit=4096, timeout=timeout, cancelled=cancelled)
        checked = validate_emitter_match(cnf, result['check']['returncode'],
                                         (output_dir / 'check.log').read_text())
        if checked != stats or sha256(table_path) != result['table_sha256']:
            raise ValueError('Input/table changed during native check')
        if (sha256(emitter) != EMITTER_SHA256
                or sha256(Path(__file__)) != result['runner_sha256']
                or sha256(Path(validator.__file__)) != result['validator_sha256']):
            raise ValueError('Emitter or validation source changed during generation')
        result.update(status='materialized', cnf_path=str(cnf), cnf_sha256=stats['sha256'],
                      cnf_bytes=stats['bytes'], variables=stats['variables'], clauses=stats['clauses'])
    except BaseException as error:
        result.update(status='ERROR', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        try:
            subprocess.run([docker, 'rm', '-f', name], capture_output=True, timeout=15)
            check = subprocess.run([docker, 'ps', '-aq', '--filter', f'name={name}'],
                                   capture_output=True, text=True, timeout=15, check=True)
            cleanup = not check.stdout.strip()
        except BaseException as error:
            cleanup = False
            result['cleanup_error'] = str(error)
        result['container_absent'] = cleanup
        if not cleanup:
            result['status'] = 'ERROR'
        with (output_dir / 'receipt.json').open('x') as destination:
            json.dump(result, destination, indent=2)
            destination.write('\n')
    if not cleanup:
        raise RuntimeError('Owned container cleanup not verified')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--case-id', required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--emitter', type=Path, default=DEFAULT_EMITTER)
    parser.add_argument('--docker', default='/usr/local/bin/docker')
    parser.add_argument('--timeout', type=int, default=120)
    args = parser.parse_args()
    def abort(signum, frame):
        raise KeyboardInterrupt(f'Input stage interrupted by signal {signum}')
    signal.signal(signal.SIGTERM, abort)
    result = materialize(args.manifest, args.manifest_sha256, args.case_id, args.output_dir,
                         emitter=args.emitter, docker=args.docker, timeout=args.timeout)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
