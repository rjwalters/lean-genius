"""Independent, read-only audit of the cloud environment probe."""
import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess

import common
import probe_container
from validate_artifacts import digest, read, require


def timestamp(value):
    # Docker uses nanosecond RFC3339, while the builder's Python accepts at
    # most microsecond precision. Preserve the timezone and truncate sub-us.
    value = value.replace('Z', '+00:00')
    value = re.sub(r'(\.\d{6})\d+(?=[+-])', r'\1', value)
    return datetime.fromisoformat(value)


def validate(created, terminal, run, environment, repo):
    require(run['schema'] == 'erdos85-h3-container-probe-v1' and
            run['production_native_search'] is False, 'Wrong probe scope')
    require(created['Id'] == terminal['Id'] == run['container_id'], 'Container identity changed')
    require(created['Name'] == terminal['Name'] == '/' + run['name'], 'Container name changed')
    require(created['State']['Status'] == 'created' and not created['State']['Running'],
            'Missing pre-start inspection')
    require(created['Image'] == terminal['Image'] == probe_container.IMAGE, 'Wrong image')
    # This Docker daemon serializes the default OOM-killer setting as false
    # before start and null after exit. Neither disables it; true is forbidden.
    def normalized_host(host):
        value = host['OomKillDisable']
        require(value is False or value is None, 'OOM killer was disabled')
        return {k: v for k, v in host.items() if k != 'OomKillDisable'}
    require(created['Config'] == terminal['Config'] and
            normalized_host(created['HostConfig']) == normalized_host(terminal['HostConfig']),
            'Container configuration changed')
    config, host = created['Config'], created['HostConfig']
    require(config['Image'] == probe_container.IMAGE and config['Entrypoint'] is None and
            config['WorkingDir'] == '/workspace/proofs', 'Wrong image command context')
    expected_command = ['lake', 'env', 'python3', '-B', '-c', probe_container.PROBE]
    require(config['Cmd'] == expected_command, 'Wrong probe command')
    require(set(config['Env']) == {
        'PATH=/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',
        'DEBIAN_FRONTEND=noninteractive', 'LEAN_NUM_THREADS=1', 'PYTHONDONTWRITEBYTECODE=1'},
        'Unexpected container environment')
    require(host['Memory'] == host['MemorySwap'] == 2 * 1024**3 and
            host['CpuQuota'] == 200000 and host['CpuPeriod'] == 100000 and
            host['NanoCpus'] == 0 and host['PidsLimit'] == 128, 'Wrong resource limits')
    require(host['ReadonlyRootfs'] is True and host['NetworkMode'] == 'none' and
            host['Privileged'] is False, 'Wrong root or network settings')
    require(host['Tmpfs'] == {'/tmp': 'rw,nosuid,size=268435456'}, 'Wrong temporary filesystem')
    require(host['RestartPolicy']['Name'] == 'no' and terminal['RestartCount'] == 0,
            'Unexpected restart policy or restart')
    require(created['Mounts'] == terminal['Mounts'], 'Mount configuration changed')
    actual_mounts = sorted((m['Type'], m.get('Name') if m['Type'] == 'volume' else m['Source'],
                            m['Destination'], m['RW']) for m in created['Mounts'])
    expected_mounts = sorted([
        ('bind', str(repo), '/workspace', False),
        ('volume', probe_container.BUILD, '/workspace/proofs/.lake/build', False),
        ('volume', probe_container.PACKAGES, '/workspace/proofs/.lake/packages', False)])
    require(actual_mounts == expected_mounts, 'Wrong or writable mounted input')
    state = terminal['State']
    require(state['Status'] == 'exited' and state['Running'] is False and
            state['Pid'] == 0 and state['ExitCode'] == 0 and state['OOMKilled'] is False,
            'No successful terminal container evidence')
    start = timestamp(state['StartedAt'])
    finish = timestamp(state['FinishedAt'])
    elapsed = (finish - start).total_seconds()
    require(0 <= elapsed <= 45 and run['wall_cap_seconds'] == 45, 'Probe exceeded wall cap')
    require(environment['limits'] == {'memory.max': str(2 * 1024**3), 'memory.swap.max': '0',
                                      'cpu.max': '200000 100000'}, 'Cgroup observation differs')
    require(environment['toolchain'] == (repo / 'proofs/lean-toolchain').read_text().strip(),
            'Toolchain differs from checkout')
    require(environment['lake_manifest_sha256'] == digest(repo / 'proofs/lake-manifest.json'),
            'Lake manifest differs from checkout')
    require(environment['lean_version'].startswith('Lean (version 4.31.0,'), 'Wrong Lean version')
    paths = environment['lean_path'].split(':')
    require(paths[-2:] == ['/workspace/proofs/.lake/build/lib/lean',
                           '/root/.elan/toolchains/leanprover--lean4---v4.31.0/lib/lean'] and
            all(p.startswith('/workspace/proofs/.lake/packages/') for p in paths[:-2]),
            'Unexpected inherited Lean search path')
    return {'container_runtime_seconds': elapsed, 'image_id': created['Image'],
            'read_only_inputs': True, 'memory_bytes': host['Memory'], 'cpu_limit': 2,
            'container_exit': 0, 'lean_version': environment['lean_version'],
            'inherited_lean_path': environment['lean_path']}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repository', type=Path, required=True)
    p.add_argument('--job', required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    repo, output = a.repository.resolve(), a.output.resolve()
    job = Path('/opt/e85/jobs') / a.job
    require((job / 'exit').read_text().strip() == '0', 'No successful outer job exit')
    run = read(output / 'RUN.json')
    expected_files = {'created.json', 'terminal.json', 'container.stdout', 'container.stderr',
                      'create.stdout', 'create.stderr'}
    require(set(run['files_sha256']) == expected_files, 'Incomplete artifact inventory')
    for name, sha in run['files_sha256'].items():
        require(digest(output / name) == sha, 'Changed probe artifact: ' + name)
    created, = read(output / 'created.json')
    terminal, = read(output / 'terminal.json')
    environment = read(output / 'container.stdout')
    require((output / 'container.stderr').read_bytes() == b'' and
            (output / 'create.stderr').read_bytes() == b'', 'Unexpected probe diagnostics')
    require((output / 'create.stdout').read_text().strip() == run['container_id'], 'Creation ID differs')
    log = (job / 'log').read_text()
    commit = re.search(r'^\[e85\] commit ([0-9a-f]{40}) ', log, re.M)[1]
    require(commit == run['execution_commit'], 'Execution commit differs')
    relative = 'research/problems/erdos-85-wip-01/h3_triple_campaign_20261008/probe_container.py'
    source = subprocess.check_output(['git', '-C', str(repo), 'show', commit + ':' + relative])
    require(hashlib.sha256(source).hexdigest() == run['source_sha256'] == digest(repo / relative),
            'Executed probe source changed')
    checked = validate(created, terminal, run, environment, repo)
    # A successful empty listing establishes removal; an observation failure
    # must not be mistaken for a missing container.
    remaining = subprocess.check_output(['docker', 'ps', '-a', '--filter',
                                          'name=^/' + run['name'] + '$', '-q'], text=True)
    require(remaining.strip() == '', 'Probe container was not removed')
    print(json.dumps({'status': 'ENVIRONMENT_PROBE_AUDIT_PASS', 'job': a.job,
        'execution_commit': commit, 'authoritative_exit': 0, 'run_sha256': digest(output / 'RUN.json'),
        'job_log_sha256': digest(job / 'log'), 'checked': checked,
        'probe_container_removed': True, 'production_native_search': False,
        'scope': 'Pinned image, read-only mounts, actual resource limits and successful environment setup. '
                 'No worker proof compilation, cache provenance approval or production credit.'}, indent=2))


if __name__ == '__main__':
    main()
