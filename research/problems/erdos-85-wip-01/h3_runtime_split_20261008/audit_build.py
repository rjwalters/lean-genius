"""Read-only audit of the H3 triple conditional chain on the cloud builder.

No Lean execution, build, cancellation, restart, or shared-source modification.
Objects stay on the builder; raw job records and sources are returned as bytes.
"""
import base64
from datetime import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPO = Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
JOB = Path('/opt/e85/jobs/20261008T115540-erdos85__h3-triple-formal-20261007-472600')
EXECUTION = '3247ac5b9e10d688214d3de9f5f0a2d6442dc087'
REVIEW = '3247ac5b9e10d688214d3de9f5f0a2d6442dc087'
CACHE = Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs')
EXPECTED = {
    'Erdos85H3TripleCompletionRuntime': [],
    'Erdos85H3TripleCompletionEngine': ['search_sound'],
    'Erdos85H3TripleCompletionBridge': ['threeHighCanonicalRepresentativeExcluded_one_of_tripleSearch',
                           'orderFortyNineTripleCellExcluded_three_one_of_tripleSearch'],
    'Erdos85H3TripleCompletionSplit': ['orderFortyNineTripleCellExcluded_three_one_of_parts'],
}
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_source(commit, relative):
    return subprocess.check_output(['git', '-C', str(REPO), 'show', commit + ':' + relative])


def object_info(path):
    script = ('import pathlib,hashlib,json; p=pathlib.Path(__import__("sys").argv[1]); '
              's=p.stat(); print(json.dumps({"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),'
              '"bytes":s.st_size,"mtime":s.st_mtime}))')
    return json.loads(subprocess.check_output(['sudo', 'python3', '-c', script, str(path)], text=True))


def main():
    require(JOB.joinpath('exit').read_text().strip() == '0', 'No authoritative successful exit')
    raw = JOB.joinpath('log').read_bytes()
    log = raw.decode()
    require(re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ', log, re.M) == [EXECUTION], 'Wrong execution commit')
    require(re.search(r'Build completed successfully \(\d+ jobs\)\.', log) is not None and '=== Build succeeded ===' in log,
            'Missing completed build')
    require(not re.search(r'\berror:', log, re.I) and 'sorry' not in log.lower(), 'Compiler failure or sorry')
    match = re.search(r'^\[e85\] job .* started (\S+)', log, re.M)
    require(match is not None, 'Missing job start')
    start = datetime.fromisoformat(match[1].replace('Z', '+00:00')).timestamp()
    finish = JOB.joinpath('exit').stat().st_mtime
    files = {'job.' + n: JOB.joinpath(n).read_bytes() for n in ('log', 'spec', 'exit')}
    results = []
    for module, suffixes in EXPECTED.items():
        relative = 'proofs/Proofs/' + module + '.lean'
        source = git_source(EXECUTION, relative)
        require(source == git_source(REVIEW, relative) == REPO.joinpath(relative).read_bytes(),
                'Reviewed/executed/current source differs: ' + module)
        text = source.decode()
        require(not re.search(r'\b(sorry|axiom|unsafe|implemented_by)\b', text),
                'Unreviewed trust escape in source: ' + module)
        names = ['Erdos85.H3TripleCompletion.' + suffix for suffix in suffixes]
        require(re.findall(r'^#print axioms (\S+)\s*$', text, re.M) == names, 'Source export inventory differs')
        built = re.findall(r'\] Built Proofs\.' + module + r' \(([^)]+)\)', log)
        require(len(built) == 1, 'Expected one fresh build: ' + module)
        pattern = (r"info: Proofs/" + module + r"\.lean:\d+:\d+: '([^'\n]+)' "
                   r'depends on axioms: \[([^\]]*)\]')
        reports = []
        for theorem, body in re.findall(pattern, log):
            axioms = [a.strip() for a in body.split(',') if a.strip()]
            require(len(axioms) == len(set(axioms)) and set(axioms) == STANDARD,
                    'Wrong axiom set: ' + theorem)
            reports.append({'theorem': theorem, 'axioms': axioms})
        require([r['theorem'] for r in reports] == names, 'Wrong raw axiom reports: ' + module)
        obj = object_info(CACHE / (module + '.olean'))
        require(obj['bytes'] > 0 and start <= obj['mtime'] <= finish,
                'Object missing or not from the successful job interval: ' + module)
        files[module + '.lean'] = source
        results.append({'module': module, 'source_sha256': sha(source),
                        'olean_sha256': obj['sha256'], 'olean_bytes': obj['bytes'],
                        'olean_mtime': obj['mtime'], 'fresh_build_elapsed': built[0],
                        'axiom_exports': reports})
    for result in results:
        module = result['module']
        require(REPO.joinpath('proofs/Proofs/' + module + '.lean').read_bytes() == files[module + '.lean'],
                'Source changed during audit')
        require(object_info(CACHE / (module + '.olean'))['sha256'] == result['olean_sha256'],
                'Object changed during audit')
    require(JOB.joinpath('log').read_bytes() == raw, 'Raw build log changed')
    cpath = CACHE.parents[2] / 'ir/Proofs/Erdos85H3TripleCompletionRuntime.c'
    cinfo = object_info(cpath)
    require(cinfo['bytes'] > 0 and start <= cinfo['mtime'] <= finish, 'Runtime C outside build interval')
    require(object_info(cpath) == cinfo, 'Runtime C changed during audit')
    audit = {'status': 'RUNTIME_SPLIT_CHAIN_BUILD_AUDIT_PASS', 'runtime_c': cinfo, 'job': JOB.name,
             'execution_commit': EXECUTION, 'review_commit': REVIEW, 'authoritative_exit': 0,
             'job_log_sha256': sha(raw),
             'retained_files_sha256': {name: sha(data) for name, data in files.items()},
             'results': results, 'scope': 'Fresh Runtime, Engine, conditional Bridge and conditional '
             'm-way composition theorem only. No native part result or unconditional triple exclusion.'}
    print(json.dumps({'audit': audit, 'files_base64': {
        name: base64.b64encode(data).decode() for name, data in files.items()}}, indent=2))


if __name__ == '__main__':
    main()
