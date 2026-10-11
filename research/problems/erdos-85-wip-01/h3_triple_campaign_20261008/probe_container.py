"""Cloud-only bounded image/mount probe. No Lean compilation or native search.

Capture raw Docker creation and terminal inspections before removing our own
stopped container. This checks whether the existing Lake environment works with
read-only repository, package and build mounts plus a read-only image root.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import uuid

import common

IMAGE = 'sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6'
BUILD = 'lean-build-erdos85__h3-triple-formal-20261007'
PACKAGES = 'lean-mathlib-packages'
PROBE = """import hashlib,json,os,pathlib,subprocess
p=pathlib.Path('/sys/fs/cgroup')
print(json.dumps({'lean_path':os.environ.get('LEAN_PATH',''),
'path':os.environ.get('PATH',''),
'toolchain':pathlib.Path('lean-toolchain').read_text().strip(),
'lake_manifest_sha256':hashlib.sha256(pathlib.Path('lake-manifest.json').read_bytes()).hexdigest(),
'lean_version':subprocess.check_output(['lean','--version'],text=True).strip(),
'limits':{n:(p/n).read_text().strip() for n in ['memory.max','memory.swap.max','cpu.max']}}))
"""


def write(path, obj):
    path.write_text(json.dumps(obj, indent=2) + '\n')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if platform.system() != 'Linux' or not Path('/opt/e85/jobs').is_dir():
        raise SystemExit('Run only on the existing cloud builder host')
    repo = common.REPO.resolve()
    if str(repo) != '/opt/e85/wt/erdos85__h3-triple-formal-20261007':
        raise SystemExit('Probe is pinned to the owned, idle triple worktree')
    output = a.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    name = 'h3-triple-probe-' + uuid.uuid4().hex
    command = ['docker', 'create', '--name', name, '--network', 'none', '--read-only',
               '--memory', str(2 * 1024**3), '--memory-swap', str(2 * 1024**3),
               '--cpu-period', '100000', '--cpu-quota', '200000', '--pids-limit', '128',
               '--tmpfs', '/tmp:rw,nosuid,size=268435456',
               '--env', 'PYTHONDONTWRITEBYTECODE=1', '--env', 'LEAN_NUM_THREADS=1',
               '--mount', f'type=bind,source={repo},target=/workspace,readonly',
               '--mount', f'type=volume,source={BUILD},target=/workspace/proofs/.lake/build,readonly',
               '--mount', f'type=volume,source={PACKAGES},target=/workspace/proofs/.lake/packages,readonly',
               '--workdir', '/workspace/proofs', IMAGE,
               'lake', 'env', 'python3', '-B', '-c', PROBE]
    receipt = {'schema': 'erdos85-h3-container-probe-v1', 'status': 'RUNNING',
               'name': name, 'started_utc': datetime.now(timezone.utc).isoformat(),
               'execution_commit': subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip(),
               'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'command': command, 'wall_cap_seconds': 45, 'production_native_search': False}
    write(output / 'RUN.json', receipt)
    created = False
    def interrupted(signum, frame):
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=30)
        (output / 'create.stdout').write_text(result.stdout)
        (output / 'create.stderr').write_text(result.stderr)
        if result.returncode:
            raise RuntimeError('Docker create failed: ' + result.stderr)
        created = True
        receipt['container_id'] = result.stdout.strip()
        before = subprocess.check_output(['docker', 'inspect', name])
        (output / 'created.json').write_bytes(before)
        subprocess.run(['docker', 'start', name], check=True, capture_output=True, timeout=15)
        try:
            waited = subprocess.run(['docker', 'wait', name], capture_output=True, text=True, timeout=45)
            if waited.returncode:
                raise RuntimeError('Docker wait failed: ' + waited.stderr)
            receipt['container_exit'] = int(waited.stdout.strip())
        except subprocess.TimeoutExpired:
            receipt['status'] = 'TIMEOUT'
            subprocess.run(['docker', 'kill', name], capture_output=True, check=True, timeout=15)
            subprocess.run(['docker', 'wait', name], capture_output=True, check=True, timeout=15)
        terminal = subprocess.check_output(['docker', 'inspect', name])
        (output / 'terminal.json').write_bytes(terminal)
        state = json.loads(terminal)[0]['State']
        if state['Running'] or state['Status'] not in ('exited', 'dead'):
            raise RuntimeError('Container is not authoritatively terminal')
        log = subprocess.run(['docker', 'logs', name], capture_output=True, check=True)
        (output / 'container.stdout').write_bytes(log.stdout)
        (output / 'container.stderr').write_bytes(log.stderr)
        if receipt['status'] != 'TIMEOUT':
            receipt['status'] = 'PROBE_PASS' if state['ExitCode'] == 0 and not state['OOMKilled'] else 'PROBE_FAILURE'
        receipt['finished_utc'] = datetime.now(timezone.utc).isoformat()
        receipt['files_sha256'] = {f.name: hashlib.sha256(f.read_bytes()).hexdigest()
                                   for f in output.iterdir() if f.is_file() and f.name != 'RUN.json'}
        write(output / 'RUN.json', receipt)
        print(json.dumps(receipt), flush=True)
        return 0 if receipt['status'] == 'PROBE_PASS' else 1
    finally:
        if created:
            # This unique container belongs to this invocation, never a peer.
            state = json.loads(subprocess.check_output(['docker', 'inspect', name]))[0]['State']
            if state['Running']:
                subprocess.run(['docker', 'kill', name], check=True, capture_output=True, timeout=15)
                subprocess.run(['docker', 'wait', name], check=True, capture_output=True, timeout=15)
            subprocess.run(['docker', 'rm', name], check=True, capture_output=True, timeout=15)


if __name__ == '__main__':
    raise SystemExit(main())
