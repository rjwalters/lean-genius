"""One bounded H3 production attempt in cloud Docker; no retries or fleet logic.

Requires a separately prepared, approved launch record and cache inventory.
Never turns its own result into AUDITED_PASS. The host collector must verify
actual execution, Docker image/mounts/limits and authoritative terminal state.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import signal
import subprocess
import time

import common
import validate_artifacts as artifacts

require, digest, read = artifacts.require, artifacts.digest, artifacts.read
CODE = ('worker.py', 'validate_artifacts.py', 'common.py', 'manifest.py')


def utc():
    return datetime.now(timezone.utc).isoformat()


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open('w') as handle:
        json.dump(value, handle, indent=2, allow_nan=False)
        handle.write('\n')
        handle.flush()
        os.fsync(handle.fileno())
    temporary.replace(path)


def bounded(command, log, env, deadline):
    """Wait for this exact child; kill and reap its process group on the cap."""
    started, started_utc = time.monotonic(), utc()
    require(started < deadline, 'Attempt deadline reached before launch')
    timed_out = False
    with log.open('x') as handle:
        child = subprocess.Popen(command, env=env, stdout=handle,
                                 stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while True:
                pid, status, usage = os.wait4(child.pid, os.WNOHANG)
                if pid:
                    break
                if time.monotonic() >= deadline:
                    timed_out = True
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    _, status, usage = os.wait4(child.pid, 0)
                    break
                time.sleep(0.1)
        except BaseException:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                _, status, usage = os.wait4(child.pid, 0)
                child.returncode = os.waitstatus_to_exitcode(status)
            except ChildProcessError:
                pass
            raise
        child.returncode = os.waitstatus_to_exitcode(status)
    return {'command': command, 'started_utc': started_utc, 'finished_utc': utc(),
            'exit_code': child.returncode, 'deadline_exceeded': timed_out,
            'elapsed_seconds': time.monotonic() - started, 'user_cpu_seconds': usage.ru_utime,
            'system_cpu_seconds': usage.ru_stime, 'max_rss_kib': usage.ru_maxrss,
            'log_sha256': digest(log)}


def validate_launch(launch, manifest):
    require(launch['schema'] == 'erdos85-h3-triple-launch-v1', 'Wrong launch schema')
    require(re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{7,127}', launch['attempt_id']) is not None,
            'Invalid attempt ID')
    require(re.fullmatch(r'[0-9a-f]{40}', launch['execution_commit']) is not None, 'Invalid commit pin')
    require(re.fullmatch(r'sha256:[0-9a-f]{64}', launch['image_id']) is not None, 'Invalid image pin')
    require(bool(launch['instance_id']) and bool(launch['slot']), 'Missing instance or slot')
    output = PurePosixPath(launch['recorded_root'])
    require(output.is_absolute() and '..' not in output.parts and
            str(output).startswith('/workspace/') and output.name == launch['attempt_id'],
            'Attempt root must be a fresh named directory under /workspace')
    limits = launch['limits']
    require(set(limits) == {'memory_bytes', 'cpu_quota_us', 'cpu_period_us', 'wall_seconds'},
            'Incomplete limits')
    require(all(type(v) is int and v > 0 for v in limits.values()), 'Invalid limits')
    require(limits['memory_bytes'] <= 16 * 1024 ** 3 and
            limits['cpu_quota_us'] <= 2 * limits['cpu_period_us'] and
            limits['wall_seconds'] <= 7200, 'Limits exceed reviewed single-attempt caps')
    require(set(launch['code_sha256']) == set(CODE), 'Incomplete worker code pins')
    for name in CODE:
        require(digest(common.PACKAGE / name) == launch['code_sha256'][name], 'Worker source changed: ' + name)
    require(manifest['schema'] == 'erdos85-h3-triple-manifest-v1', 'Wrong manifest schema')
    candidates = [c for c in manifest['cases'] if c['id'] == launch['case_id']]
    require(len(candidates) == 1 and candidates[0]['state'] == 'PENDING',
            'Case must be one uncredited manifest entry')
    case = candidates[0]
    require(common.source_hashes(case) == case['source_sha256'], 'Generated source hashes changed')
    for name, sha in manifest['generator_sha256'].items():
        require(digest(common.PACKAGE / name) == sha, 'Manifest generator changed')
    for section in ('source_inputs_sha256', 'prerequisite_sources_sha256'):
        for name, sha in manifest[section].items():
            path = common.REPO / name
            require((digest(path) if path.exists() else None) == sha, 'Pinned source changed: ' + name)
    return case


def actual_limits(root=Path('/sys/fs/cgroup')):
    cpu = (root / 'cpu.max').read_text().split()
    require(len(cpu) == 2 and cpu[0] != 'max', 'No hard CPU quota')
    memory = (root / 'memory.max').read_text().strip()
    require(memory != 'max', 'No hard memory limit')
    require((root / 'memory.swap.max').read_text().strip() == '0', 'Swap must be disabled')
    return {'memory_bytes': int(memory), 'cpu_quota_us': int(cpu[0]), 'cpu_period_us': int(cpu[1])}


def check_limits(wanted, actual):
    require(actual == {k: wanted[k] for k in actual} and len(actual) == 3,
            'Actual cgroup limits differ from launch pins')


def inventory_files(root):
    require(root.is_dir() and not root.is_symlink(), 'Invalid cache root')
    result = {}
    for p in sorted(root.rglob('*')):
        require(not p.is_symlink(), 'Linked cache entry: ' + str(p))
        if p.is_file():
            result[str(p.relative_to(root))] = digest(p)
        else:
            require(p.is_dir(), 'Non-regular cache entry')
    require(bool(result), 'Empty cache root')
    return result


def cache_roots(inventory, case, manifest):
    require(inventory['schema'] == 'erdos85-h3-triple-cache-v1', 'Wrong cache schema')
    require(inventory['manifest_sha256'] == digest(common.PACKAGE / 'MANIFEST.json'),
            'Cache inventory belongs to a different manifest')
    names = ('library', 'full_base', 'full_final') if case['branch'] == 'full' else ('library', 'deficient_base')
    require(set(inventory['roots']) == set(names), 'Wrong branch cache inventory')
    require(inventory['base_receipts'] == manifest['base_receipts'], 'Wrong census receipt pins')
    roots = {}
    for name in names:
        record = inventory['roots'][name]
        path = Path(record['path'])
        require(path.is_absolute() and '..' not in path.parts, 'Invalid cache path')
        require(inventory_files(path) == record['files'], 'Cache inventory changed: ' + name)
        roots[name] = path
    for name, receipt in (('full_base', 'full'), ('full_final', 'full_final'), ('deficient_base', 'deficient')):
        if name in roots:
            require(digest(roots[name] / 'RUN.json') == manifest['base_receipts'][receipt],
                    'Census receipt does not match audited pin')
    for relative in inventory['roots']['library']['files']:
        require(not Path(relative).name.startswith('Erdos85ThreeHighCampaign'),
                'Production seed contains campaign objects')
    for module in ('Erdos85ThreeHighNativePairSearch', 'Erdos85ThreeBlockCompactCodes',
                   'Erdos85ThreeHighSecondaryOrbitTable'):
        require((roots['library'] / 'Proofs' / (module + '.olean')).is_file(), 'Missing generic dependency')
    return roots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--launch', type=Path, required=True)
    parser.add_argument('--launch-sha256', required=True)
    parser.add_argument('--cache-inventory', type=Path, required=True)
    parser.add_argument('--stop-file', type=Path, required=True)
    args = parser.parse_args()
    require(platform.system() == 'Linux' and Path('/.dockerenv').exists() and
            Path.cwd().resolve() == Path('/workspace/proofs'), 'Run only in cloud Docker from /workspace/proofs')
    require(digest(args.launch) == args.launch_sha256, 'Launch record changed')
    launch = read(args.launch)
    manifest_path = common.PACKAGE / 'MANIFEST.json'
    require(digest(manifest_path) == launch['manifest_sha256'], 'Wrong manifest pin')
    manifest = read(manifest_path)
    case = validate_launch(launch, manifest)
    limits = actual_limits()
    check_limits(launch['limits'], limits)
    require(digest(args.cache_inventory) == launch['cache_inventory_sha256'], 'Cache inventory pin mismatch')
    cache = read(args.cache_inventory)
    require(not args.stop_file.exists(), 'STOP before attempt creation')
    output = Path(launch['recorded_root'])
    output.mkdir(parents=True, exist_ok=False)
    receipt = {'schema': 'erdos85-h3-triple-receipt-v1', 'status': 'RUNNING',
               'production_native_search': True, 'manifest_sha256': launch['manifest_sha256'],
               'case_id': case['id'], 'attempt_id': launch['attempt_id'],
               'recorded_root': str(output), 'launch_sha256': args.launch_sha256,
               'cache_inventory_sha256': launch['cache_inventory_sha256'],
               'started_utc': utc(), 'actual_limits': limits, 'results': [],
               'scope': 'Worker result only; independent host and artifact audit required.'}
    deadline = time.monotonic() + launch['limits']['wall_seconds']
    save = lambda: atomic_json(output / 'RUN.json', receipt)
    save()
    shutil.copyfile(args.launch, output / 'LAUNCH.json')
    shutil.copyfile(args.cache_inventory, output / 'CACHE.json')

    def stop_or_timeout():
        if args.stop_file.exists():
            receipt['status'] = 'STOPPED'
        elif time.monotonic() >= deadline:
            receipt['status'] = 'TIMEOUT'
        else:
            return False
        receipt['finished_utc'] = utc()
        save()
        return True

    try:
        roots = cache_roots(cache, case, manifest)
        if stop_or_timeout():
            return 1
        # A complete namespace copy avoids both shadowing and shared writes.
        private = output / 'library'
        result = bounded(['cp', '-a', '--reflink=auto', str(roots['library']), str(private)],
                         output / 'cache-copy.log', os.environ.copy(), deadline)
        receipt['cache_copy'] = result
        save()
        require(result['exit_code'] == 0, 'Private cache copy failed')
        require(inventory_files(private) == cache['roots']['library']['files'], 'Private cache copy changed')
        source_root, directory = output / 'source-root/Proofs', output / case['id']
        source_root.mkdir(parents=True)
        directory.mkdir()
        for name, text in common.sources(case).items():
            (directory / name).write_text(text)
        env = os.environ.copy()
        env['LEAN_NUM_THREADS'] = '1'
        imports = [str(private), str(directory)] + [str(roots[n]) for n in roots if n != 'library']
        # The launch host must pin the inherited Lake/package search path.
        require(env.get('LEAN_PATH', '') == launch['inherited_lean_path'], 'Unexpected inherited Lean path')
        env['LEAN_PATH'] = os.pathsep.join(imports + [launch['inherited_lean_path']])
        receipt['lean_path'] = env['LEAN_PATH']
        for stage in artifacts.STAGES:
            if stop_or_timeout():
                return 1
            check_limits(launch['limits'], actual_limits())
            name = case['module_prefix'] + stage
            source = directory / (name + '.lean')
            is_library = stage in ('Inputs', 'Certificate')
            if is_library:
                shutil.copyfile(source, source_root / source.name)
            cmd = artifacts.command(case, stage, str(output))
            obj = Path(cmd[4])
            require(not obj.exists(), 'Refuse to overwrite a pre-existing output')
            receipt['active_stage'] = stage
            save()
            entry = bounded(cmd, directory / (name + '.log'), env, deadline)
            if obj.is_file() and is_library:
                # Retain the certificate before any consumer work or validation.
                shutil.copyfile(obj, directory / obj.name)
            log = (directory / (name + '.log')).read_text()
            try:
                exports = artifacts.reports(log)
            except ValueError:
                exports = []
            entry.update(case_id=case['id'], module=name, stage=stage,
                         source_sha256=digest(source), olean_sha256=digest(obj) if obj.is_file() else None,
                         axiom_exports=exports, certificate_substitution=False)
            atomic_json(directory / (name + '.run.json'), entry)
            receipt['results'].append(entry)
            receipt.pop('active_stage')
            save()
            try:
                artifacts.validate_stage(directory, case, stage, entry, str(output))
            except (ValueError, OSError, KeyError) as error:
                # A failed certificate may be a real counterexample. Until its
                # raw diagnostic is reviewed, do not call it resource failure.
                receipt['status'] = ('TIMEOUT' if entry['deadline_exceeded'] else
                                     'ALARM' if stage == 'Certificate' else 'ERROR')
                receipt['validation_error'] = str(error)
                receipt['finished_utc'] = utc()
                save()
                return 1
            if stage == 'Certificate':
                receipt['status'] = 'CERTIFICATE_RETAINED'
                save()
            print(json.dumps({'case': case['id'], 'stage': stage, 'status': 'VALIDATED'}), flush=True)
        require(validate_launch(launch, manifest) == case, 'Source snapshot changed')
        require(cache_roots(cache, case, manifest) == roots, 'Imported cache changed')
        require(digest(args.launch) == args.launch_sha256 and
                digest(args.cache_inventory) == launch['cache_inventory_sha256'], 'Input records changed')
        artifacts.validate_bundle(manifest_path, launch['manifest_sha256'], case['id'], output, str(output))
        receipt['status'] = 'WORKER_PASS'
        receipt['finished_utc'] = utc()
        save()
        return 0
    except BaseException as error:
        receipt['status'] = 'ERROR'
        receipt['error'] = type(error).__name__ + ': ' + str(error)
        receipt['finished_utc'] = utc()
        save()
        raise


if __name__ == '__main__':
    raise SystemExit(main())
