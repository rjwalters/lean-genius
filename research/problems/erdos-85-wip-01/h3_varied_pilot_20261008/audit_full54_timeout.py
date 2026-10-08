"""Retain and audit the terminal FullU54R20 timeout; never restart a search."""
import base64
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPO = Path('/opt/e85/wt/erdos85__h3-first-column-20261008')
REL = Path('research/problems/erdos-85-wip-01/h3_varied_pilot_20261008')
OUTPUT = REPO / REL / '_build/FullU54R20-first'
JOB = Path('/opt/e85/jobs/20261008T064336-erdos85__h3-first-column-20261008-270638')
COMMIT = '9a1555a52461ab6d53bb145378f92de81c88cdc6'
PREFIX = 'Erdos85ThreeHighPilotFullU54R20'
SOURCE_SHA = {
    'Inputs': '324653ac84cdf0a257221e3a495ace46b96e64a73e5d5f2fd3d0de1071f2bd38',
    'Certificate': 'be3a4ac1b4700915860fc4507ef4df4c725439b8ba7bb47870791c3037125f28',
    'Consumer': '1d0aa08a664fa59a2d0cee5564d6d49e4b37b12280aef646f41777e37ef5ea3e'}


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    require((JOB / 'exit').read_text().strip() == '124', 'No authoritative timeout exit')
    log = (JOB / 'log').read_text()
    require(re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ', log, re.M) == [COMMIT] and
            '[7200s] Building...' in log and 'Timeout exceeded, stopping container...' in log,
            'Wrong source or missing timeout event')
    files = {'job.' + n: (JOB / n).read_bytes() for n in ('log', 'exit', 'spec')}
    for path in OUTPUT.iterdir():
        require(path.is_file() and not path.is_symlink(), 'Unexpected output entry')
        files[path.name] = path.read_bytes()
    run = json.loads(files['RUN.json'])
    require(run['status'] == 'RUNNING' and run['active_module'] == PREFIX + 'Certificate' and
            len(run['results']) == 1 and run['results'][0]['module'] == PREFIX + 'Inputs',
            'Unexpected partial receipt; review manually')
    item = run['results'][0]
    require(item['exit_code'] == 0 and item['status'] == 'PASS' and item['axiom_exports'] == [] and
            item['log_sha256'] == sha(files[PREFIX + 'Inputs.log']) and
            item['source_sha256'] == SOURCE_SHA['Inputs'], 'Input receipt differs')
    for stage, expected in SOURCE_SHA.items():
        name = PREFIX + stage + '.lean'
        source = subprocess.check_output(['git', '-C', str(REPO), 'show', COMMIT + ':' + str(REL / name)])
        require(sha(source) == expected and source == (REPO / REL / name).read_bytes(), 'Source changed: ' + name)
        if name in files:
            require(files[name] == source, 'Executed source differs: ' + name)
        else:
            files['unexecuted-' + name] = source
    require(PREFIX + 'Certificate.run.json' not in files and PREFIX + 'Consumer.run.json' not in files,
            'Unexpected later stage receipt')
    cache = '/var/lib/docker/volumes/lean-build-erdos85__h3-first-column-20261008/_data/lib/lean/Proofs'
    script = ('import pathlib,json,hashlib; p=pathlib.Path(' + repr(cache) + '); '
              'print(json.dumps({s: {"exists": (p/(' + repr(PREFIX) + '+s+".olean")).is_file(), '
              '"sha256": hashlib.sha256((p/(' + repr(PREFIX) + '+s+".olean")).read_bytes()).hexdigest() '
              'if (p/(' + repr(PREFIX) + '+s+".olean")).is_file() else None} '
              'for s in ("Inputs","Certificate","Consumer")}))')
    objects = json.loads(subprocess.check_output(['sudo', 'python3', '-c', script], text=True))
    require(objects['Inputs']['sha256'] == item['olean_sha256'] and
            not objects['Certificate']['exists'] and not objects['Consumer']['exists'],
            'Object inventory differs; do not infer absence of completed work')
    remaining = subprocess.check_output(['docker', 'ps', '-a', '--filter', 'name=^/lean-build-270892$', '-q'], text=True)
    require(not remaining.strip(), 'Timed-out container still exists')
    process = subprocess.run(['ps', '-p', '270666,271444', '-o', 'pid='], capture_output=True, text=True)
    require(process.returncode == 1 and not process.stdout.strip(), 'Old runner/compiler still present')
    audit = {'status': 'TIMEOUT_OBSERVATION_AUDIT_PASS', 'case': 'FullU54R20',
        'job': JOB.name, 'execution_commit': COMMIT, 'authoritative_exit': 124,
        'terminal_classification': 'TIMEOUT', 'outer_cap_seconds': 7200,
        'raw_run_status': run['status'], 'active_module_at_cutoff': run['active_module'],
        'auditor_sha256': sha(Path(__file__).read_bytes()),
        'files_sha256': {name: sha(data) for name, data in files.items()},
        'objects': objects, 'container_removed': True, 'old_runner_and_compiler_absent': True,
        'completed_stages': ['Inputs'], 'new_rejection_credit': False, 'retry_authorized': False,
        'scope': 'Right-censored selected diagnostic at the outer two-hour cap. '
                 'No successful Certificate/Consumer object or receipt. Original RUN.json is retained '
                 'unchanged even though the outer runner is terminal. No counterexample or OOM is inferred.'}
    print(json.dumps({'audit': audit, 'files_base64': {
        name: base64.b64encode(data).decode() for name, data in files.items()}}, indent=2))


if __name__ == '__main__':
    main()
