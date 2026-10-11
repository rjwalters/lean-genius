"""Read-only audit of the H5 conditional chain on the cloud builder.

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

REPO = Path('/opt/e85/wt/erdos85__h5-formal-20261008')
JOB = Path('/opt/e85/jobs/20261008T112110-erdos85__h5-formal-20261008-450285')
EXECUTION = 'f7117ae8d261c6a0ad7176503983d6938532c1ae'
REVIEW = '99bc3e3413008ca13d5efb29bee5e855af961976'
CACHE = Path('/var/lib/docker/volumes/lean-build-erdos85__h5-formal-20261008/_data/lib/lean/Proofs')
EXPECTED = {'Erdos85H5Fast': ['searchF_sound', 'fiveHighCanonicalRepresentativeExcluded_of_partsF']}

STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
PRIOR = [{'module': 'Erdos85H3PairEngine', 'source_sha256': '6f84fc3a0de0bbc170d98b7a85824b1c84282fbcf4f2824267cac96bf3b37625', 'olean_sha256': '35c3cba5f6e9e8526ecc31c6471e591baafbe9a816641e50856b882cef440222', 'olean_bytes': 2095936, 'olean_mtime': 1791455014.379877, 'fresh_build_elapsed': '9.8s', 'axiom_exports': [{'theorem': 'Erdos85.H3Pair.search_sound', 'axioms': ['propext', 'Classical.choice', 'Quot.sound']}]}, {'module': 'Erdos85H5Engine', 'source_sha256': '7e39050eeef3acda6f578a321a148873961e3a09b332776806cc3236b842638a', 'olean_sha256': 'a70da513a95fac71dbab06bcedf1d91faf6bbce1aa24585c246d276d03a9af4e', 'olean_bytes': 2492824, 'olean_mtime': 1791455026.030168, 'fresh_build_elapsed': '11s', 'axiom_exports': [{'theorem': 'Erdos85.H5.search_sound', 'axioms': ['propext', 'Classical.choice', 'Quot.sound']}, {'theorem': 'Erdos85.H5.parts_sound', 'axioms': ['propext', 'Classical.choice', 'Quot.sound']}]}, {'module': 'Erdos85H5Bridge', 'source_sha256': '81f0128eb80a6509f30c2962636d1865678480f167c7ad01fd890f34851b3205', 'olean_sha256': '1ecb095d48ef4b380851a8c57e177fe01f51d1dd543007dc52cfcb271cefcd3c', 'olean_bytes': 207608, 'olean_mtime': 1791455037.3504512, 'fresh_build_elapsed': '8.6s', 'axiom_exports': [{'theorem': 'Erdos85.H5.model_of_constraints', 'axioms': ['propext', 'Classical.choice', 'Quot.sound']}, {'theorem': 'Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_of_parts', 'axioms': ['propext', 'Classical.choice', 'Quot.sound']}]}]


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
    require('Build completed successfully (8748 jobs).' in log and '=== Build succeeded ===' in log,
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
        namespace = 'Erdos85.H3Pair.' if module == 'Erdos85H3PairEngine' else 'Erdos85.H5.'
        names = [namespace + suffix for suffix in suffixes]
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
    prerequisites=[]
    for item in PRIOR:
        module=item['module']
        relative='proofs/Proofs/'+module+'.lean'
        data=REPO.joinpath(relative).read_bytes()
        require(data==git_source(EXECUTION,relative)==git_source(REVIEW,relative), 'Prerequisite source drift')
        require(sha(data)==item['source_sha256'], 'Prerequisite differs from earlier independent audit')
        require(object_info(CACHE/(module+'.olean'))['sha256']==item['olean_sha256'], 'Prerequisite object drift')
        prerequisites.append({'module':module,'source_sha256':item['source_sha256'],'olean_sha256':item['olean_sha256']})
    require(JOB.joinpath('log').read_bytes() == raw, 'Raw build log changed')
    audit = {'status': 'H5_FAST_LINK_BUILD_AUDIT_PASS', 'job': JOB.name,
             'execution_commit': EXECUTION, 'review_commit': REVIEW, 'authoritative_exit': 0,
             'job_log_sha256': sha(raw),
             'retained_files_sha256': {name: sha(data) for name, data in files.items()},
             'results': results, 'prerequisites':prerequisites, 'scope': 'Fresh H5Fast conditional soundness link only; prior audited prerequisites unchanged. No native-premise or whole-stratum verdict.'}
    print(json.dumps({'audit': audit, 'files_base64': {
        name: base64.b64encode(data).decode() for name, data in files.items()}}, indent=2))


if __name__ == '__main__':
    main()
