"""Terminal-only read-only H3 pair audit on the existing builder.

No Lean execution or source mutation. Refuses an absent/nonzero job exit.
Accepts the earlier conditional-chain AUDIT.json as JSON on stdin.
"""
import base64
from datetime import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

REPO = Path('/opt/e85/wt/erdos85__h3-pair-formal-20261008')
JOB = Path('/opt/e85/jobs/20261008T081713-erdos85__h3-pair-formal-20261008-331716')
COMMIT = 'b3545ac16ae75faa072a66400bedb087544a03bf'
CACHE = Path('/var/lib/docker/volumes/lean-build-erdos85__h3-pair-formal-20261008/_data/lib/lean/Proofs')
PARTS = [f'Erdos85H3PairPart{i:02d}' for i in range(24)]
NATIVE = {f'Erdos85.H3Pair.pairPart_24_{i:02d}._native.native_decide.ax_1_1' for i in range(24)}
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
EXPORTS = ['Erdos85.H3Pair.threeHighCanonicalRepresentativeExcluded_zero',
           'Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero']
CELL = 'Erdos85H3PairCell'


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def objects(names):
    script = '''import hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1]);out={}
for n in sys.argv[2:]:
 p=root/(n+'.olean');s=p.stat();b=p.read_bytes()
 out[n]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'mtime':s.st_mtime}
print(json.dumps(out))'''
    return json.loads(subprocess.check_output(['sudo', 'python3', '-c', script, str(CACHE), *names]))


def main():
    require((JOB / 'exit').exists(), 'Producer has no terminal exit; wait for the same job')
    require((JOB / 'exit').read_text().strip() == '0', 'Producer did not succeed')
    prior_raw = sys.stdin.buffer.read()
    prior = json.loads(prior_raw)
    require(prior['status'] == 'CONDITIONAL_SPLIT_CHAIN_BUILD_AUDIT_PASS' and
            prior['review_commit'] == COMMIT and
            prior['job_log_sha256'] == 'aaf39843475db3cf5e297e63b425c1b49f88b2e92c75b0e142b1eac6fef5b320',
            'Wrong conditional prerequisite report')
    old = {r['module']: r for r in prior['results']}
    require(set(old) == {'Erdos85H3PairEngine', 'Erdos85H3PairBridge', 'Erdos85H3PairSplit'},
            'Wrong prerequisite module inventory')
    raw = (JOB / 'log').read_bytes()
    log = raw.decode()
    require(re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ', log, re.M) == [COMMIT], 'Wrong producer source')
    require('Build completed successfully' in log and '=== Build succeeded ===' in log,
            'Missing successful build trailer')
    require(not re.search(r'\berror:', log, re.I) and 'sorry' not in log.lower(), 'Error or sorry in build')
    match = re.search(r'^\[e85\] job .* started (\S+)', log, re.M)
    require(match is not None, 'Missing producer start time')
    start = datetime.fromisoformat(match[1].replace('Z', '+00:00')).timestamp()
    finish = (JOB / 'exit').stat().st_mtime
    fresh = PARTS + [CELL]
    names = list(old) + fresh
    first = objects(names)
    files = {'job.' + n: (JOB / n).read_bytes() for n in ['log', 'spec', 'exit']}
    files['prior-conditional-audit.json'] = prior_raw
    results = []
    for module in names:
        path = 'proofs/Proofs/' + module + '.lean'
        source = subprocess.check_output(['git', '-C', str(REPO), 'show', COMMIT + ':' + path])
        require(source == (REPO / path).read_bytes(), 'Source differs from execution pin: ' + module)
        text = source.decode()
        require(not re.search(r'\b(sorry|unsafe|implemented_by)\b', text), 'Unreviewed source escape: ' + module)
        require(not re.search(r'^\s*(?:private\s+)?axiom\s', text, re.M), 'Explicit source axiom: ' + module)
        obj = first[module]
        require(obj['bytes'] > 0, 'Empty object: ' + module)
        if module in old:
            require(sha(source) == old[module]['source_sha256'] and
                    obj['sha256'] == old[module]['olean_sha256'], 'Conditional prerequisite changed: ' + module)
        else:
            require(start <= obj['mtime'] <= finish, 'Object outside producer time interval: ' + module)
            built = re.findall(r'\] Built Proofs\.' + re.escape(module) + r' \(([^)]+)\)', log)
            require(len(built) == 1, 'Not exactly one fresh module build: ' + module)
        if module in PARTS:
            i = PARTS.index(module)
            require(re.findall(r'^import (\S+)', text, re.M) == ['Proofs.Erdos85H3PairSplit'], 'Wrong part import')
            require(re.findall(r'theorem\s+(pairPart_24_\d+)\s*:\s*pairPart\s+24\s+(\d+)\s*=\s*true', text) ==
                    [(f'pairPart_24_{i:02d}', str(i))], 'Wrong part theorem/index')
            require(len(re.findall(r'^\s+native_decide\s*$', text, re.M)) == 1, 'Wrong native proof shape')
        files['sources/' + module + '.lean'] = source
        results.append({'module': module, 'source_sha256': sha(source), 'object': obj,
                        'fresh_in_producer': module in fresh})
    cell_source = files['sources/' + CELL + '.lean'].decode()
    require(re.findall(r'^import (\S+)', cell_source, re.M) == ['Proofs.' + n for n in PARTS], 'Incomplete Cell imports')
    require(re.findall(r'^#print axioms (\S+)\s*$', cell_source, re.M) == EXPORTS, 'Wrong Cell exports')
    pattern = r"info: Proofs/Erdos85H3PairCell\.lean:\d+:\d+: '([^'\n]+)' depends on axioms: \[([^\]]*)\]"
    reports = []
    for theorem, body in re.findall(pattern, log):
        axioms = [a.strip() for a in body.split(',') if a.strip()]
        require(len(axioms) == len(set(axioms)) and set(axioms) == STANDARD | NATIVE,
                'Unexpected final axiom set for ' + theorem + ': ' + repr(axioms))
        reports.append({'theorem': theorem, 'axioms': axioms})
    require([r['theorem'] for r in reports] == EXPORTS, 'Missing final raw axiom reports')
    require(objects(names) == first, 'Objects changed during audit')
    require((JOB / 'log').read_bytes() == raw, 'Producer log changed during audit')
    for module in names:
        require((REPO / ('proofs/Proofs/' + module + '.lean')).read_bytes() == files['sources/' + module + '.lean'],
                'Source changed during audit: ' + module)
    audit = {'status': 'H3_PAIR_CELL_TERMINAL_AUDIT_PASS', 'producer_job': JOB.name,
             'producer_commit': COMMIT, 'authoritative_exit': 0, 'fresh_parts': 24,
             'results': results, 'axiom_exports': reports,
             'retained_sha256': {n: sha(b) for n, b in files.items()},
             'scope': 'Unconditional native-backed pair cell (3,0) only; not the remaining H3 triple profile or full drop.'}
    print(json.dumps({'audit': audit, 'files': {n: base64.b64encode(b).decode() for n, b in files.items()}}))


if __name__ == '__main__':
    main()
