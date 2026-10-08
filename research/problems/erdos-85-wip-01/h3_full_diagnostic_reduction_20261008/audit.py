"""Read-only audit of the actual Full259/Full258 composition artifacts."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repository', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--prior-build', type=Path, required=True)
    p.add_argument('--prerequisites', type=Path, required=True)
    p.add_argument('--extra-objects', type=Path, required=True)
    p.add_argument('--through', choices=['Full259', 'Full258'], required=True)
    p.add_argument('--full54-receipt-sha256')
    a = p.parse_args()
    repository, output = a.repository.resolve(), a.output.resolve()
    package = repository / 'research/problems/erdos-85-wip-01/h3_full_diagnostic_reduction_20261008'
    spec = importlib.util.spec_from_file_location('composition', package / 'check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    run_sha = sha(output / 'RUN.json')
    run = read(output / 'RUN.json')
    require(run['status'] == 'PASS' and run['through'] == a.through, 'Wrong completion or stage')
    library, copies, provenance = checker.validate(a.prior_build.resolve(), a.prerequisites.resolve(),
        a.extra_objects.resolve(), a.full54_receipt_sha256, a.through)
    require(run['provenance'] == provenance, 'Changed prerequisite evidence')
    count = 259 if a.through == 'Full259' else 258
    scope = ('Two' if count == 259 else 'Three') + f' prior full certificates consumed; {count} rejection hypotheses remain.'
    require(run['scope'] == scope, 'Scope mismatch')
    modules = ['Full259'] if count == 259 else ['Full259', 'Full258']
    require([e['module'] for e in run['results']] == modules, 'Wrong compiled inventory')
    if count == 259:
        require(not any(output.glob('Full258.*')), 'Unexpected Full258 artifact')
    dep = run['dependencies']
    require(dep['exit_code'] == 0 and dep['command'] == ['lake', 'build', *library]
            and dep['log_sha256'] == sha(output / 'dependencies.log'), 'Dependency mismatch')
    require(not set(dep['command']) & {'Proofs.' + name for _, name, _ in copies}, 'Imported object rebuilt')
    recorded = Path('/workspace') / output.relative_to(repository)
    standard = {'propext', 'Classical.choice', 'Quot.sound'}
    u1 = 'Erdos85.NativeTerminalPilot.rejected._native.native_decide.ax_1_1'
    u3 = 'Erdos85.VariedPilot.FullU3R3.rejected._native.native_decide.ax_1_1'
    u54 = 'Erdos85.VariedPilot.FullU54R20.rejected._native.native_decide.ax_1_1'
    results = []
    for e in run['results']:
        name = e['module']
        source = package / (name + '.lean')
        require(e['status'] == 'PASS' and e['exit_code'] == 0
                and read(output / (name + '.run.json')) == e, 'Individual receipt mismatch')
        require(sha(source) == sha(output / source.name) == e['source_sha256'], 'Source mismatch')
        require(sha(output / (name + '.olean')) == e['olean_sha256'], 'Object mismatch')
        logpath = output / (name + '.log')
        require(sha(logpath) == e['log_sha256'], 'Log mismatch')
        require(e['command'] == ['lean', '-R', str(recorded), '-o', str(recorded / (name + '.olean')),
                                str(recorded / (name + '.lean'))], 'Compiler command mismatch')
        log = logpath.read_text()
        require('sorry' not in log.lower(), 'Sorry in log')
        reports = [{'theorem': n, 'axioms': [v.strip() for v in (ax or '').split(',') if v.strip()]}
                   for n, ax in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", log)]
        namespace = 'FullUStrongAfterTwoPilots' if name == 'Full259' else 'FullUStrongAfterThreePilots'
        names = [namespace + '.' + n for n in ['pilot_mem', 'remainingPairs_card', 'pilot_input',
                 'pilot_rejected', 'actual_distinct_witness', 'excluded_of_rejections']]
        require([r['theorem'] for r in reports] == names and reports == e['axiom_exports'], 'Export mismatch')
        require(re.findall(r'^#print axioms (\S+)\s*$', source.read_text(), re.M) == names, 'Source exports changed')
        current = u3 if name == 'Full259' else u54
        inherited = {u1} if name == 'Full259' else {u1, u3}
        for i, report in enumerate(reports):
            expected = standard | ({current} if i == 3 else inherited | {current} if i >= 4 else set())
            require(set(report['axioms']) == expected, 'Unexpected trust set')
        results.append({k: e[k] for k in ['module', 'source_sha256', 'olean_sha256', 'log_sha256',
                       'axiom_exports', 'elapsed_seconds', 'user_cpu_seconds', 'system_cpu_seconds', 'max_rss_kib']})
    require(sha(output / 'RUN.json') == run_sha, 'Receipt changed during audit')
    print(json.dumps({'status': 'PASS', 'through': a.through, 'run_sha256': run_sha,
                      'provenance': provenance, 'results': results, 'scope': scope}, indent=2))


if __name__ == '__main__':
    main()
