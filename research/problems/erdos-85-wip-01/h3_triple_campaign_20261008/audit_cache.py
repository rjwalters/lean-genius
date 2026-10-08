"""Read-only cloud host audit of worker cache preparation and retained snapshots."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

import common
import canary
import prepare_cache
from validate_artifacts import digest, read, require


def actual_files(root):
    """Walk actual files independently of the worker's inventory helper."""
    require(root.is_dir() and not root.is_symlink(), 'Invalid retained root')
    result = {}
    for parent, dirs, files in os.walk(root):
        for name in dirs + files:
            require(not (Path(parent) / name).is_symlink(), 'Linked retained artifact')
        for name in files:
            path = Path(parent) / name
            require(path.is_file(), 'Non-file retained artifact')
            result[str(path.relative_to(root))] = digest(path)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repository', type=Path, required=True)
    p.add_argument('--job', required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    repo, output = a.repository.resolve(), a.output.resolve()
    require(repo == common.REPO, 'Auditor imported a different checkout')
    job = Path('/opt/e85/jobs') / a.job
    require((job / 'exit').read_text().strip() == '0', 'No successful terminal exit')
    raw_log = (job / 'log').read_text()
    commit = re.search(r'^\[e85\] commit ([0-9a-f]{40}) ', raw_log, re.M)[1]
    run = read(output / 'RUN.json')
    require(run['schema'] == 'erdos85-h3-cache-preparation-v1' and run['status'] == 'CACHE_PREPARED'
            and run['production_native_search'] is False, 'Wrong preparation scope')
    manifest = canary.verify_manifest(run['manifest_sha256'])
    roots, prior_audit = prepare_cache.validate_census(manifest)
    require(prior_audit == run['census_audit'], 'Prior census validation differs')
    code_pins = {}
    for name in ('prepare_cache.py', 'worker.py', 'validate_artifacts.py', 'common.py', 'manifest.py', 'canary.py'):
        path = common.PACKAGE / name
        source = subprocess.check_output(['git', '-C', str(repo), 'show', commit + ':' + str(path.relative_to(repo))])
        require(source == path.read_bytes(), 'Preparation code changed: ' + name)
        code_pins[name] = digest(path)
    require(run['source_sha256'] == code_pins['prepare_cache.py'], 'Wrong preparation script')
    for label in ('dependencies', 'copy'):
        entry = run[label]
        log = output / (label + '.log')
        require(entry['exit_code'] == 0 and entry['deadline_exceeded'] is False, 'Failed preparation stage')
        require(entry['log_sha256'] == digest(log), 'Changed preparation log')
    require(run['dependencies']['command'] == ['lake', 'build', *prepare_cache.LIBRARY],
            'Unexpected dependency build targets')
    recorded = Path('/workspace') / output.relative_to(repo)
    require(run['copy']['command'] == ['cp', '-a', '--reflink=auto',
        '/workspace/proofs/.lake/build/lib/lean', str(recorded / 'library')], 'Unexpected library copy')
    checked = {}
    for branch, names in [('full', ('library', 'full_base', 'full_final')),
                          ('deficient', ('library', 'deficient_base'))]:
        path = output / ('CACHE-' + branch + '.json')
        cache = read(path)
        require(digest(path) == run['inventories'][branch]['sha256'], 'Cache inventory hash differs')
        require(cache['schema'] == 'erdos85-h3-triple-cache-v1' and
                cache['manifest_sha256'] == run['manifest_sha256'] and
                cache['base_receipts'] == manifest['base_receipts'], 'Wrong cache binding')
        require(set(cache['roots']) == set(names), 'Unexpected cache roots')
        counts = {}
        for name in names:
            record = cache['roots'][name]
            recorded_path = Path(record['path'])
            require(recorded_path.is_relative_to('/workspace'), 'Invalid recorded cache path')
            actual = repo / recorded_path.relative_to('/workspace')
            expected = output / 'library' if name == 'library' else roots[name]
            require(actual == expected, 'Cache root differs from approved preparation input')
            files = actual_files(actual)
            require(files == record['files'], 'Retained cache inventory differs: ' + name)
            counts[name] = len(files)
            if name == 'library':
                require(not any(Path(n).name.startswith('Erdos85ThreeHighCampaign') for n in files),
                        'Campaign objects in seed library')
        require(counts == run['inventories'][branch]['files'], 'Wrong cache file counts')
        checked[branch] = {'sha256': digest(path), 'files': counts}
    print(json.dumps({'status': 'CACHE_ARTIFACT_AUDIT_PASS', 'job': a.job,
        'execution_commit': commit, 'authoritative_exit': 0, 'run_sha256': digest(output / 'RUN.json'),
        'job_log_sha256': digest(job / 'log'), 'manifest_sha256': run['manifest_sha256'],
        'code_sha256': code_pins, 'inventories': checked, 'census_audit': prior_audit,
        'production_native_search': False,
        'scope': 'Prepared cache bytes, generic dependency build and previously audited census artifacts. '
                 'Uses the established builder/toolchain cache; no clean Mathlib rebuild or new rejection.'}, indent=2))


if __name__ == '__main__':
    main()
