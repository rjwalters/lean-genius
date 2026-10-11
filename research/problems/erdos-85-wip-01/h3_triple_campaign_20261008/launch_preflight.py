"""Launch exactly one non-native worker preflight on the existing cloud builder.

The sole writable bind mount is the fresh attempt-output parent. Inputs use the
audited snapshot and read-only repository/packages/build mounts. Retain Docker
creation/terminal records and logs before removing our unique stopped container.
No fleet, retry, native Certificate stage, or claim mutation is implemented here.
"""
import argparse
import json
from pathlib import Path
import platform
import signal
import socket
import subprocess
import uuid

import common
import probe_container
import worker

require, digest, read = worker.require, worker.digest, worker.read
REPO = Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
INSTANCE = 'i-04a61ff360a07bef2'


def recorded(path):
    return Path('/workspace') / path.relative_to(REPO)


def launch_record(case, output, manifest_sha, cache_sha, inherited, commit):
    attempt_id = 'preflight-' + uuid.uuid4().hex
    return {'schema': 'erdos85-h3-triple-launch-v1', 'mode': 'preflight',
            'attempt_id': attempt_id, 'case_id': case['id'], 'manifest_sha256': manifest_sha,
            'recorded_root': str(recorded(output / 'work' / attempt_id)),
            'execution_commit': commit, 'image_id': probe_container.IMAGE,
            'instance_id': INSTANCE, 'slot': 'owned-triple-preflight',
            'limits': {'memory_bytes': 16 * 1024**3, 'cpu_quota_us': 200000,
                       'cpu_period_us': 100000, 'wall_seconds': 600},
            'code_sha256': {n: digest(common.PACKAGE / n) for n in worker.CODE},
            'cache_inventory_sha256': cache_sha, 'inherited_lean_path': inherited}


def docker_command(name, output, launch_sha):
    package = recorded(common.PACKAGE)
    out = recorded(output)
    return ['docker', 'create', '--name', name, '--network', 'none', '--read-only',
        '--memory', str(16 * 1024**3), '--memory-swap', str(16 * 1024**3),
        '--cpu-period', '100000', '--cpu-quota', '200000', '--pids-limit', '256',
        '--tmpfs', '/tmp:rw,nosuid,size=1073741824',
        '--env', 'PYTHONDONTWRITEBYTECODE=1', '--env', 'LEAN_NUM_THREADS=1',
        '--mount', f'type=bind,source={REPO},target=/workspace,readonly',
        '--mount', f'type=volume,source={probe_container.BUILD},target=/workspace/proofs/.lake/build,readonly',
        '--mount', f'type=volume,source={probe_container.PACKAGES},target=/workspace/proofs/.lake/packages,readonly',
        '--mount', f'type=bind,source={output / "work"},target={out / "work"}',
        '--workdir', '/workspace/proofs', probe_container.IMAGE,
        'lake', 'env', 'python3', '-B', str(package / 'worker.py'),
        '--launch', str(out / 'LAUNCH.json'), '--launch-sha256', launch_sha,
        '--cache-inventory', str(out / 'CACHE.json'), '--stop-file', str(out / 'STOP')]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--case', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    require(platform.system() == 'Linux' and Path('/opt/e85/jobs').is_dir() and
            common.REPO == REPO, 'Run only on the owned existing cloud builder worktree')
    manifest_path = common.PACKAGE / 'MANIFEST.json'
    require(digest(manifest_path) == a.manifest_sha256, 'Manifest pin mismatch')
    manifest = read(manifest_path)
    cases = [c for c in manifest['cases'] if c['id'] == a.case]
    require(len(cases) == 1 and cases[0]['state'] == 'PENDING', 'Select one uncredited manifest case')
    case = cases[0]
    require(case['id'] != 'full-u054-r20', 'Do not overlap the running diagnostic')
    output = a.output.resolve()
    require(output.is_relative_to(common.PACKAGE / '_build'), 'Output must stay in the owned build area')
    require(not subprocess.check_output(['git', '-C', str(REPO), 'status', '--porcelain',
                                        '--untracked-files=no'], text=True).strip(), 'Tracked checkout is dirty')
    commit = subprocess.check_output(['git', '-C', str(REPO), 'rev-parse', 'HEAD'], text=True).strip()
    approval = read(common.PACKAGE / 'cache-preparation-evidence/AUDIT.json')
    require(approval['status'] == 'CACHE_ARTIFACT_AUDIT_PASS' and
            approval['manifest_sha256'] == a.manifest_sha256, 'Missing matching cache audit')
    cache_path = common.PACKAGE / '_build/cache-preflight-first' / ('CACHE-' + case['branch'] + '.json')
    cache_sha = approval['inventories'][case['branch']]['sha256']
    require(digest(cache_path) == cache_sha, 'Audited cache inventory differs')
    probe = read(common.PACKAGE / 'container-probe-evidence/AUDIT.json')
    require(probe['status'] == 'ENVIRONMENT_PROBE_AUDIT_PASS' and
            probe['checked']['image_id'] == probe_container.IMAGE, 'Missing pinned environment audit')
    # Reserve headroom on the existing host; this does not allocate new nodes.
    meminfo = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
    require(int(meminfo['MemAvailable'].split()[0]) >= 28 * 1024**2,
            'Insufficient available memory for 16 GiB plus 12 GiB host headroom')
    launch = launch_record(case, output, a.manifest_sha256, cache_sha,
                           probe['checked']['inherited_lean_path'], commit)
    worker.validate_launch(launch, manifest)
    output.mkdir(parents=True, exist_ok=False)
    (output / 'work').mkdir()
    worker.atomic_json(output / 'LAUNCH.json', launch)
    (output / 'CACHE.json').write_bytes(cache_path.read_bytes())
    launch_sha = digest(output / 'LAUNCH.json')
    name = 'h3-worker-' + launch['attempt_id']
    command = docker_command(name, output, launch_sha)
    receipt = {'schema': 'erdos85-h3-preflight-host-v1', 'status': 'RUNNING',
               'started_utc': worker.utc(), 'hostname': socket.gethostname(),
               'execution_commit': commit, 'case_id': case['id'], 'container_name': name,
               'launch_sha256': launch_sha, 'command': command, 'wall_cap_seconds': 660,
               'source_sha256': digest(Path(__file__)), 'production_native_search': False}
    save = lambda: worker.atomic_json(output / 'HOST.json', receipt)
    save()
    created = False
    def interrupted(signum, frame):
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=30)
        (output / 'create.stdout').write_text(result.stdout)
        (output / 'create.stderr').write_text(result.stderr)
        require(result.returncode == 0, 'Docker create failed: ' + result.stderr)
        created = True
        receipt['container_id'] = result.stdout.strip()
        (output / 'created.json').write_bytes(subprocess.check_output(['docker', 'inspect', name]))
        subprocess.run(['docker', 'start', name], check=True, capture_output=True, timeout=15)
        try:
            waited = subprocess.run(['docker', 'wait', name], capture_output=True, text=True, timeout=660)
            require(waited.returncode == 0, 'Docker wait failed: ' + waited.stderr)
            receipt['container_exit'] = int(waited.stdout.strip())
        except subprocess.TimeoutExpired:
            receipt['status'] = 'TIMEOUT'
            subprocess.run(['docker', 'kill', name], check=True, capture_output=True, timeout=15)
            subprocess.run(['docker', 'wait', name], check=True, capture_output=True, timeout=15)
        terminal = subprocess.check_output(['docker', 'inspect', name])
        (output / 'terminal.json').write_bytes(terminal)
        state = json.loads(terminal)[0]['State']
        require(not state['Running'] and state['Status'] in ('exited', 'dead'), 'No terminal container state')
        log = subprocess.run(['docker', 'logs', name], check=True, capture_output=True)
        (output / 'container.stdout').write_bytes(log.stdout)
        (output / 'container.stderr').write_bytes(log.stderr)
        if receipt['status'] != 'TIMEOUT':
            receipt['status'] = 'CONTAINER_EXIT_ZERO' if state['ExitCode'] == 0 and not state['OOMKilled'] else 'ERROR'
        receipt['finished_utc'] = worker.utc()
        receipt['files_sha256'] = {f.name: digest(f) for f in output.iterdir()
                                   if f.is_file() and f.name != 'HOST.json'}
        save()
        print(json.dumps(receipt), flush=True)
        return 0 if receipt['status'] == 'CONTAINER_EXIT_ZERO' else 1
    except BaseException as error:
        receipt['status'] = 'ERROR'
        receipt['error'] = type(error).__name__ + ': ' + str(error)
        receipt['finished_utc'] = worker.utc()
        save()
        raise
    finally:
        if created:
            state = json.loads(subprocess.check_output(['docker', 'inspect', name]))[0]['State']
            if state['Running']:
                subprocess.run(['docker', 'kill', name], check=True, capture_output=True, timeout=15)
                subprocess.run(['docker', 'wait', name], check=True, capture_output=True, timeout=15)
            # Retain terminal evidence even if interrupted before normal collection.
            (output / 'terminal.json').write_bytes(subprocess.check_output(['docker', 'inspect', name]))
            log = subprocess.run(['docker', 'logs', name], check=True, capture_output=True)
            (output / 'container.stdout').write_bytes(log.stdout)
            (output / 'container.stderr').write_bytes(log.stderr)
            subprocess.run(['docker', 'rm', name], check=True, capture_output=True, timeout=15)
            receipt['container_removed'] = True
            receipt['files_sha256'] = {f.name: digest(f) for f in output.iterdir()
                                       if f.is_file() and f.name != 'HOST.json'}
            save()


if __name__ == '__main__':
    raise SystemExit(main())
