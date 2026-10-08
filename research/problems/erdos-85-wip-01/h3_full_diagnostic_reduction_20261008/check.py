"""Cloud-only connection of the two independently audited full diagnostic pairs."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent
RESEARCH = PACKAGE.parent
PREVIOUS = RESEARCH / 'h3_u1r15_census_reduction_20261008'
VARIED = RESEARCH / 'h3_varied_pilot_20261008'
PRIOR_SHA = '36fe58d9bae19306311cc9655d0300a3ecf60e669141c4fe834e89be670de820'
CENSUS_SHA = 'dd262a3d974d3da91d5365dd88d7668183f55cb6083a5dca803588ba517217cb'
FIRST_SHA = '1a59f0543cf7ee4ddf31c88a9efd2a15585310a14d333f6281e8abce91eb43d0'
NATIVE_U1 = 'Erdos85.NativeTerminalPilot.rejected._native.native_decide.ax_1_1'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


previous = load('full_previous', PREVIOUS / 'check.py')
timing = previous.timing
require, digest = previous.require, timing.digest


def read(path):
    return json.loads(path.read_text())


def native(case):
    return 'Erdos85.VariedPilot.' + case + '.rejected._native.native_decide.ax_1_1'


def validate(prior_build, prerequisites, extra, second_sha):
    require(re.fullmatch(r'[0-9a-f]{64}', second_sha) is not None, 'Final independently audited receipt hash required')
    require(digest(prior_build / 'RUN.json') == PRIOR_SHA, 'Wrong Full260 build')
    require(read(PREVIOUS / 'evidence/AUDIT.json')['status'] == 'PASS'
            and read(PREVIOUS / 'evidence/AUDIT.json')['run_sha256'] == PRIOR_SHA, 'Full260 lacks independent audit')
    repository = RESEARCH.parents[2]
    audited = subprocess.run([sys.executable, '-B', str(PREVIOUS / 'audit.py'), '--repository', str(repository),
        '--output', str(prior_build), '--prerequisites', str(prerequisites),
        '--final-receipt-sha256', CENSUS_SHA], capture_output=True, text=True)
    require(audited.returncode == 0, 'Prior artifact audit failed: ' + audited.stderr)
    prior_audit = json.loads(audited.stdout)
    require(prior_audit['status'] == 'PASS' and prior_audit['run_sha256'] == PRIOR_SHA, 'Prior audit mismatch')
    objects, _ = previous.imported_objects(prerequisites / 'extra')
    copies = [(prerequisites / 'extra' / (name + '.olean'), name, sha) for name, sha in objects.items()]
    cases = []
    for case_name, expected_sha in [('FullU3R3', FIRST_SHA), ('FullU54R20', second_sha)]:
        case, membership_sha = timing.preflight(case_name, PREVIOUS / 'evidence')
        evidence = VARIED / (case_name + '-evidence')
        require(digest(evidence / 'RUN.json') == expected_sha, 'Changed diagnostic receipt')
        audit, run = read(evidence / 'AUDIT.json'), read(evidence / 'RUN.json')
        require(audit['status'] == run['status'] == 'PASS' and audit['run_sha256'] == expected_sha, 'Diagnostic lacks independent audit')
        require(run['case'] == case and run['preflight_sha256'] == membership_sha == PRIOR_SHA, 'Diagnostic case or membership mismatch')
        require([e['module'] for e in run['results']] == [case['module_prefix'] + s for s in ['Inputs', 'Certificate', 'Consumer']], 'Diagnostic inventory mismatch')
        for e in run['results']:
            name = e['module']
            require(e['status'] == 'PASS' and e['exit_code'] == 0, 'Failed diagnostic module')
            require(read(evidence / (name + '.run.json')) == e, 'Individual receipt mismatch')
            require(digest(evidence / (name + '.lean')) == e['source_sha256'] == digest(VARIED / (name + '.lean')), 'Diagnostic source mismatch')
            require(digest(evidence / (name + '.log')) == e['log_sha256'], 'Diagnostic log mismatch')
            if name.endswith('Certificate') or name.endswith('Consumer'):
                theorem = case['namespace'] + ('.rejected' if name.endswith('Certificate') else '.no_joint')
                reports = [r for r in timing.reports((evidence / (name + '.log')).read_text()) if r['theorem'] == theorem]
                require(reports == e['axiom_exports'] and len(reports) == 1
                        and set(reports[0]['axioms']) == timing.STANDARD | {native(case_name)}, 'Diagnostic trust mismatch')
            if name.endswith('Certificate'):
                obj = extra / (name + '.olean')
                require(digest(obj) == e['olean_sha256'], 'Diagnostic object mismatch')
                copies.append((obj, name, e['olean_sha256']))
        cases.append({'case': case_name, 'receipt_sha256': expected_sha})
    library = read(prior_build / 'RUN.json')['dependencies']['command']
    require(library[:2] == ['lake', 'build'], 'Unexpected dependency command')
    return library[2:], copies, {'prior_receipt_sha256': PRIOR_SHA, 'census_receipt_sha256': CENSUS_SHA,
        'diagnostics': cases, 'prior_audit': prior_audit,
        'imported_object_sha256': {name: sha for _, name, sha in copies}}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--prior-build', type=Path, required=True)
    p.add_argument('--prerequisites', type=Path, required=True)
    p.add_argument('--extra-objects', type=Path, required=True)
    p.add_argument('--full54-receipt-sha256', required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    require(Path('/.dockerenv').exists() and Path('Proofs').is_dir(), 'Run only inside cloud Docker from proofs')
    prior, prerequisites, extra, output = [v.resolve() for v in (a.prior_build, a.prerequisites, a.extra_objects, a.output)]
    library, copies, provenance = validate(prior, prerequisites, extra, a.full54_receipt_sha256)
    output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    receipt = {'status': 'RUNNING', 'provenance': provenance, 'results': [],
               'scope': 'Three prior full certificates consumed; 258 rejection hypotheses remain.'}

    def save():
        tmp = output / 'RUN.json.tmp'
        tmp.write_text(json.dumps(receipt, indent=2) + '\n')
        tmp.replace(output / 'RUN.json')

    save()
    require(not set(library) & {'Proofs.' + name for _, name, _ in copies}, 'Refuse to rebuild imported objects')
    receipt['dependencies'] = timing.run(['lake', 'build', *library], output / 'dependencies.log', env)
    save()
    if receipt['dependencies']['exit_code']:
        receipt['status'] = 'DEPENDENCY_FAILURE'
        save()
        return 1
    root = Path('.lake/build/lib/lean/Proofs').resolve()
    for src, name, sha in copies:
        dst = root / (name + '.olean')
        if dst.exists():
            require(digest(dst) == sha, 'Refuse to replace different library object')
        else:
            shutil.copyfile(src, dst)
        require(digest(dst) == sha, 'Object copy mismatch')
    env['LEAN_PATH'] = os.pathsep.join([str(output), str(prior), str(prerequisites / 'final'), str(prerequisites / 'base'), env.get('LEAN_PATH', '')])
    for name, current, inherited in [('Full259', 'FullU3R3', {NATIVE_U1}),
                                     ('Full258', 'FullU54R20', {NATIVE_U1, native('FullU3R3')})]:
        source = PACKAGE / (name + '.lean')
        target = output / source.name
        shutil.copyfile(source, target)
        log, obj = target.with_suffix('.log'), target.with_suffix('.olean')
        result = timing.run(['lean', '-R', str(output), '-o', str(obj), str(target)], log, env)
        reports = timing.reports(log.read_text())
        wanted = re.findall(r'^#print axioms (\S+)\s*$', source.read_text(), re.M)
        passed = (result['exit_code'] == 0 and obj.is_file() and source.read_bytes() == target.read_bytes()
                  and 'sorry' not in log.read_text().lower()
                  and [r['theorem'] for r in reports] == wanted and len(wanted) == 6)
        for i, report in enumerate(reports):
            expected = timing.STANDARD | ({native(current)} if i == 3 else inherited | {native(current)} if i >= 4 else set())
            passed = passed and set(report['axioms']) == expected
        result.update(module=name, status='PASS' if passed else 'FAIL', source_sha256=digest(source),
                      olean_sha256=digest(obj) if obj.is_file() else None, axiom_exports=reports)
        (output / (name + '.run.json')).write_text(json.dumps(result, indent=2) + '\n')
        receipt['results'].append(result)
        save()
        print(json.dumps(result), flush=True)
        if not passed:
            receipt['status'] = 'MODULE_FAILURE'
            save()
            return 1
    require(validate(prior, prerequisites, extra, a.full54_receipt_sha256) == (library, copies, provenance), 'Prerequisites changed')
    receipt['status'] = 'PASS'
    save()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
