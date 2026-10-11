"""Read-only host and artifact audit for a completed non-native worker preflight.

Run on the existing builder. This never runs Lean, launches containers, retries
work, or credits a census case. It checks raw Docker observations and actual
retained artifacts against the separately pinned launch, manifest and cache.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

import common
from audit_probe import timestamp
from validate_artifacts import digest, read, require, validate_bundle

IMAGE = 'sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6'
BUILD = 'lean-build-erdos85__h3-triple-formal-20261007'
PACKAGES = 'lean-mathlib-packages'
RELATIVE = Path('research/problems/erdos-85-wip-01/h3_triple_campaign_20261008')
LIMITS = {'memory_bytes': 16 * 1024**3, 'cpu_quota_us': 200000,
          'cpu_period_us': 100000, 'wall_seconds': 600}


def recorded(path, repo):
    return str(Path('/workspace') / path.relative_to(repo))


def host_path(value, repo):
    path = Path(value)
    require(path.is_absolute() and '..' not in path.parts, 'Invalid recorded path')
    return repo / path.relative_to('/workspace')


def validate_container(created, terminal, host_run, launch, repo, output):
    require(created['Id'] == terminal['Id'] == host_run['container_id'], 'Wrong container ID')
    name = 'h3-worker-' + launch['attempt_id']
    require(host_run['container_name'] == name and
            created['Name'] == terminal['Name'] == '/' + name, 'Wrong container name')
    require(created['State']['Status'] == 'created' and created['State']['Running'] is False,
            'Missing pre-start inspection')
    require(created['Image'] == terminal['Image'] == launch['image_id'] == IMAGE, 'Wrong image')
    def normalized(host):
        require(host['OomKillDisable'] is False or host['OomKillDisable'] is None,
                'OOM killer disabled')
        return {k: v for k, v in host.items() if k != 'OomKillDisable'}
    require(created['Config'] == terminal['Config'] and
            normalized(created['HostConfig']) == normalized(terminal['HostConfig']),
            'Container configuration changed')
    config, host = created['Config'], created['HostConfig']
    command = ['lake', 'env', 'python3', '-B', '/workspace/' + str(RELATIVE / 'worker.py'),
               '--launch', recorded(output / 'LAUNCH.json', repo),
               '--launch-sha256', digest(output / 'LAUNCH.json'),
               '--cache-inventory', recorded(output / 'CACHE.json', repo),
               '--stop-file', recorded(output / 'STOP', repo)]
    require(config['Cmd'] == command and config['Image'] == IMAGE and
            config['Entrypoint'] is None and config['WorkingDir'] == '/workspace/proofs',
            'Wrong worker command')
    require(set(config['Env']) == {
        'PATH=/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',
        'DEBIAN_FRONTEND=noninteractive', 'LEAN_NUM_THREADS=1', 'PYTHONDONTWRITEBYTECODE=1'},
        'Unexpected container environment')
    require(host['Memory'] == host['MemorySwap'] == LIMITS['memory_bytes'] and
            host['CpuQuota'] == LIMITS['cpu_quota_us'] and
            host['CpuPeriod'] == LIMITS['cpu_period_us'] and
            host['NanoCpus'] == 0 and host['PidsLimit'] == 256, 'Wrong hard resource limits')
    require(host['ReadonlyRootfs'] is True and host['NetworkMode'] == 'none' and
            host['Privileged'] is False, 'Wrong root or network settings')
    require(host['Tmpfs'] == {'/tmp': 'rw,nosuid,size=1073741824'}, 'Wrong tmpfs')
    require(host['RestartPolicy']['Name'] == 'no' and terminal['RestartCount'] == 0,
            'Unexpected restart')
    require(created['Mounts'] == terminal['Mounts'], 'Mounts changed')
    mounts = sorted((m['Type'], m.get('Name') if m['Type'] == 'volume' else m['Source'],
                     m['Destination'], m['RW']) for m in created['Mounts'])
    expected = sorted([
        ('bind', str(repo), '/workspace', False),
        ('volume', BUILD, '/workspace/proofs/.lake/build', False),
        ('volume', PACKAGES, '/workspace/proofs/.lake/packages', False),
        ('bind', str(output / 'work'), recorded(output / 'work', repo), True)])
    require(mounts == expected, 'Wrong mounts or writable input')
    state = terminal['State']
    require(state['Status'] == 'exited' and state['Running'] is False and state['Pid'] == 0 and
            state['ExitCode'] == 0 and state['OOMKilled'] is False, 'No successful terminal state')
    elapsed = (timestamp(state['FinishedAt']) - timestamp(state['StartedAt'])).total_seconds()
    require(0 <= elapsed <= 660 and host_run['wall_cap_seconds'] == 660,
            'Container exceeded outer wall cap')
    return elapsed


def inventory(root):
    require(root.is_dir() and not root.is_symlink(), 'Missing or linked cache root')
    files = {}
    for path in root.rglob('*'):
        require(not path.is_symlink(), 'Linked cache entry')
        if path.is_file():
            files[str(path.relative_to(root))] = digest(path)
        else:
            require(path.is_dir(), 'Non-regular cache entry')
    return files


def audit(repo, job_id, output, manifest_sha, case_id):
    package, job = repo / RELATIVE, Path('/opt/e85/jobs') / job_id
    require((job / 'exit').read_text().strip() == '0', 'Missing successful outer exit')
    manifest_path = package / 'MANIFEST.json'
    require(digest(manifest_path) == manifest_sha, 'Wrong manifest')
    manifest = read(manifest_path)
    case, = [c for c in manifest['cases'] if c['id'] == case_id and c['state'] == 'PENDING']
    launch, host_run = read(output / 'LAUNCH.json'), read(output / 'HOST.json')
    require(launch['schema'] == 'erdos85-h3-triple-launch-v1' and launch['mode'] == 'preflight' and
            launch['case_id'] == case_id and launch['manifest_sha256'] == manifest_sha and
            launch['limits'] == LIMITS and launch['instance_id'] == 'i-04a61ff360a07bef2' and
            launch['slot'] == 'owned-triple-preflight', 'Wrong launch identity or scope')
    require(re.fullmatch(r'preflight-[0-9a-f]{32}', launch['attempt_id']) is not None,
            'Wrong attempt identifier')
    attempt = output / 'work' / launch['attempt_id']
    require(launch['recorded_root'] == recorded(attempt, repo), 'Wrong attempt root')
    require(host_run['schema'] == 'erdos85-h3-preflight-host-v1' and
            host_run['status'] == 'CONTAINER_EXIT_ZERO' and host_run['container_exit'] == 0 and
            host_run['production_native_search'] is False and host_run['container_removed'] is True and
            host_run['case_id'] == case_id and host_run['launch_sha256'] == digest(output / 'LAUNCH.json'),
            'Wrong host result')
    expected_files = {'LAUNCH.json', 'CACHE.json', 'created.json', 'terminal.json',
                      'container.stdout', 'container.stderr', 'create.stdout', 'create.stderr'}
    require(set(host_run['files_sha256']) == expected_files, 'Wrong host artifact inventory')
    for name, sha in host_run['files_sha256'].items():
        require(digest(output / name) == sha, 'Host artifact changed: ' + name)
    require((output / 'create.stdout').read_text().strip() == host_run['container_id'] and
            (output / 'create.stderr').read_bytes() == b'' and
            (output / 'container.stderr').read_bytes() == b'', 'Unexpected Docker diagnostics')
    created, = read(output / 'created.json')
    terminal, = read(output / 'terminal.json')
    elapsed = validate_container(created, terminal, host_run, launch, repo, output)
    raw_log = (job / 'log').read_text()
    commits = re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ', raw_log, re.M)
    require(len(commits) == 1, 'Missing or ambiguous execution commit')
    commit, = commits
    require(commit == launch['execution_commit'] == host_run['execution_commit'], 'Commit differs')
    require(set(launch['code_sha256']) == {'worker.py', 'validate_artifacts.py', 'common.py', 'manifest.py'},
            'Wrong worker code inventory')
    pins = dict(launch['code_sha256'], **{'launch_preflight.py': host_run['source_sha256']})
    sources = {str(RELATIVE / name): sha for name, sha in pins.items()}
    sources[str(RELATIVE / 'MANIFEST.json')] = manifest_sha
    sources.update(manifest['source_inputs_sha256'])
    sources.update(manifest['prerequisite_sources_sha256'])
    for relative, sha in sources.items():
        if sha is None:
            listed = subprocess.check_output(['git', '-C', str(repo), 'ls-tree', '--name-only',
                                              commit, '--', relative], text=True)
            require(not listed.strip() and not (repo / relative).exists(),
                    'Expected absent source exists: ' + relative)
            continue
        source = subprocess.check_output(['git', '-C', str(repo), 'show', commit + ':' + relative])
        require(hashlib.sha256(source).hexdigest() == sha == digest(repo / relative),
                'Execution source changed: ' + relative)
    probe = read(package / 'container-probe-evidence/AUDIT.json')
    approval = read(package / 'cache-preparation-evidence/AUDIT.json')
    require(probe['status'] == 'ENVIRONMENT_PROBE_AUDIT_PASS' and
            probe['checked']['image_id'] == IMAGE and
            launch['inherited_lean_path'] == probe['checked']['inherited_lean_path'],
            'Environment audit differs')
    require(approval['status'] == 'CACHE_ARTIFACT_AUDIT_PASS' and
            approval['manifest_sha256'] == manifest_sha, 'Cache audit differs')
    cache_sha = approval['inventories'][case['branch']]['sha256']
    require(cache_sha == launch['cache_inventory_sha256'] == digest(output / 'CACHE.json'),
            'Cache pin differs')
    cache = read(output / 'CACHE.json')
    require(cache['schema'] == 'erdos85-h3-triple-cache-v1' and
            cache['manifest_sha256'] == manifest_sha and cache['base_receipts'] == manifest['base_receipts'],
            'Wrong cache provenance')
    census = ['full_final', 'full_base'] if case['branch'] == 'full' else ['deficient_base']
    require(set(cache['roots']) == {'library', *census}, 'Wrong cache roots')
    for name, entry in cache['roots'].items():
        require(inventory(host_path(entry['path'], repo)) == entry['files'], 'Cache changed: ' + name)
    run = read(attempt / 'RUN.json')
    require(run['status'] == 'PREFLIGHT_PASS' and run['mode'] == 'preflight' and
            run['launch_sha256'] == digest(output / 'LAUNCH.json') and
            run['cache_inventory_sha256'] == cache_sha and
            run['actual_limits'] == {k: v for k, v in LIMITS.items() if k != 'wall_seconds'},
            'Wrong worker result or actual limits')
    for name in ('LAUNCH.json', 'CACHE.json'):
        require((attempt / name).read_bytes() == (output / name).read_bytes(), 'Worker input differs')
    expected_path = ':'.join([recorded(attempt / 'library', repo), recorded(attempt / case_id, repo)] +
                            [cache['roots'][name]['path'] for name in census] +
                            [launch['inherited_lean_path']])
    require(run['lean_path'] == expected_path, 'Wrong compiler import path')
    worker_start, worker_end = timestamp(run['started_utc']), timestamp(run['finished_utc'])
    require(timestamp(terminal['State']['StartedAt']) <= worker_start <= worker_end <=
            timestamp(terminal['State']['FinishedAt']) and
            (worker_end - worker_start).total_seconds() <= 600, 'Wrong worker time interval')
    for stage in run['results']:
        require(stage['deadline_exceeded'] is False and
                worker_start <= timestamp(stage['started_utc']) <= timestamp(stage['finished_utc']) <= worker_end,
                'Stage exceeded deadline or escaped worker interval')
    artifacts = validate_bundle(manifest_path, manifest_sha, case_id, attempt,
                                launch['recorded_root'], preflight_only=True)
    expected_library = dict(cache['roots']['library']['files'])
    input_name = case['module_prefix'] + 'Inputs'
    expected_library['Proofs/' + input_name + '.olean'] = run['results'][0]['olean_sha256']
    require(inventory(attempt / 'library') == expected_library, 'Private library changed unexpectedly')
    require((attempt / 'source-root/Proofs' / (input_name + '.lean')).read_bytes() ==
            (attempt / case_id / (input_name + '.lean')).read_bytes(), 'Compiled input source differs')
    remaining = subprocess.check_output(['docker', 'ps', '-a', '--filter',
        'name=^/' + host_run['container_name'] + '$', '-q'], text=True)
    require(remaining.strip() == '', 'Container still exists')
    return {'status': 'WORKER_PREFLIGHT_AUDIT_PASS', 'job': job_id, 'case_id': case_id,
            'execution_commit': commit, 'manifest_sha256': manifest_sha,
            'host_sha256': digest(output / 'HOST.json'), 'run_sha256': digest(attempt / 'RUN.json'),
            'launch_sha256': digest(output / 'LAUNCH.json'), 'cache_inventory_sha256': cache_sha,
            'job_log_sha256': digest(job / 'log'), 'authoritative_exit': 0,
            'container_runtime_seconds': elapsed, 'limits': LIMITS, 'container_removed': True,
            'artifacts': artifacts, 'production_native_search': False, 'campaign_credit': False,
            'scope': 'Bounded Inputs+Membership worker execution on the audited existing cache. '
                     'No native certificate, consumer, campaign exclusion, or clean Mathlib rebuild.'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repository', type=Path, required=True)
    p.add_argument('--job', required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--case', required=True)
    a = p.parse_args()
    print(json.dumps(audit(a.repository.resolve(), a.job, a.output.resolve(),
                           a.manifest_sha256, a.case), indent=2))


if __name__ == '__main__':
    main()
