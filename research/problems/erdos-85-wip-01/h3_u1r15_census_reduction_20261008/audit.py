"""Read-only independent artifact audit of FullMembership and Full260."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repository', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--prerequisites', type=Path, required=True)
    p.add_argument('--final-receipt-sha256', required=True)
    a = p.parse_args()
    repository = a.repository.resolve()
    research = repository / 'research/problems/erdos-85-wip-01'
    package = research / 'h3_u1r15_census_reduction_20261008'
    spec = importlib.util.spec_from_file_location('checked_reduction', package / 'check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    output, prerequisites = a.output.resolve(), a.prerequisites.resolve()
    recorded = Path('/workspace') / output.relative_to(repository)
    run_sha = sha(output / 'RUN.json')
    run = read(output / 'RUN.json')
    require(run['status'] == 'PASS', 'Non-PASS build')
    library, census = checker.census(prerequisites / 'base', prerequisites / 'final', a.final_receipt_sha256)
    imported, inputs = checker.imported_objects(prerequisites / 'extra')
    require(run['census_audit'] == census and run['imported_object_sha256'] == imported, 'Prerequisite mismatch')
    require(run['pilot_receipt_sha256'] == checker.PILOT_SHA and run['input_receipt_sha256'] == checker.PREFLIGHT_SHA, 'Wrong prior receipts')
    require(run['results'][:2] == inputs and run['reused_input_modules'] == [e['module'] for e in inputs], 'Reused input receipts changed')
    require(run['plan_sha256'] == sha(output / 'PLAN.json') == sha(research / 'h3_varied_pilot_20261008/PLAN.json'), 'Plan changed')
    for e in inputs:
        for suffix, key in [('.lean', 'source_sha256'), ('.log', 'log_sha256')]:
            require(sha(output / (e['module'] + suffix)) == e[key], 'Reused input artifact changed')
    expected_library = sorted(set(library) | {'Proofs.Erdos85ThreeHighNativePairSearch', 'Proofs.Erdos85ThreeBlockCompactCodes', 'Proofs.Erdos85ThreeHighSecondaryOrbitTable'})
    dep = run['dependencies']
    require(dep['exit_code'] == 0 and dep['command'] == ['lake', 'build', *expected_library] and dep['log_sha256'] == sha(output / 'dependencies.log'), 'Dependency evidence mismatch')
    require(not set(dep['command']) & {'Proofs.' + name for name in imported}, 'Imported object rebuilt')
    require([e['module'] for e in run['results'][2:]] == ['FullMembership', 'Full260'], 'Wrong compiled inventory')
    results = []
    for e in run['results'][2:]:
        name = e['module']
        source = (research / 'h3_varied_pilot_20261008' if name == 'FullMembership' else package) / (name + '.lean')
        require(e['status'] == 'PASS' and e['exit_code'] == 0 and read(output / (name + '.run.json')) == e, 'Module receipt mismatch')
        require(sha(source) == sha(output / source.name) == e['source_sha256'], 'Source mismatch')
        require(sha(output / (name + '.olean')) == e['olean_sha256'], 'Object mismatch')
        require(sha(output / (name + '.log')) == e['log_sha256'], 'Log mismatch')
        require(e['command'] == ['lean', '-R', str(recorded), '-o', str(recorded / (name + '.olean')), str(recorded / (name + '.lean'))], 'Compiler command mismatch')
        log = (output / (name + '.log')).read_text()
        reports = [{'theorem': n, 'axioms': [v.strip() for v in (ax or '').split(',') if v.strip()]} for n, ax in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", log)]
        names = (['FullU3R3_mem', 'FullU3R3_input', 'FullU54R20_mem', 'FullU54R20_input'] if name == 'FullMembership' else ['FullUStrongAfterPilot.' + n for n in ['pilot_mem', 'remainingPairs_card', 'pilot_input', 'pilot_rejected', 'actual_distinct_witness', 'excluded_of_rejections']])
        require([r['theorem'] for r in reports] == names and reports == e['axiom_exports'], 'Axiom report inventory mismatch')
        require(re.findall(r'^#print axioms (\S+)\s*$', source.read_text(), re.M) == names, 'Source export inventory mismatch')
        require('sorry' not in log.lower(), 'Sorry in log')
        for i, r in enumerate(reports):
            expected = {'propext', 'Classical.choice', 'Quot.sound'}
            if name == 'Full260' and i >= 3:
                require(set(r['axioms']) == expected | {'Erdos85.NativeTerminalPilot.rejected._native.native_decide.ax_1_1'}, 'Unexpected native trust set')
            else:
                require(set(r['axioms']) <= expected, 'Nonstandard axiom')
        results.append({k: e[k] for k in ['module', 'source_sha256', 'olean_sha256', 'log_sha256', 'axiom_exports', 'elapsed_seconds', 'user_cpu_seconds', 'system_cpu_seconds', 'max_rss_kib']})
    require(sha(output / 'RUN.json') == run_sha, 'Receipt changed during audit')
    print(json.dumps({'status': 'PASS', 'run_sha256': run_sha, 'final_census_receipt_sha256': a.final_receipt_sha256, 'results': results, 'scope': 'Conditional 260-pair reduction and membership for two diagnostic cases; remaining rejections open.'}, indent=2))


if __name__ == '__main__':
    main()
