"""Read-only cloud-host artifact audit of the two-pilot deficient reduction."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repository', type=Path, required=True)
    p.add_argument('--job', required=True)
    a = p.parse_args()
    repo = a.repository.resolve()
    package = repo / 'research/problems/erdos-85-wip-01/h3_deficient_second_pilot_reduction_20261008'
    previous = package.parent / 'h3_deficient_pilot_reduction_20261008'
    output = package / '_build/cloud-first'
    job = Path('/opt/e85/jobs') / a.job
    assert (job / 'exit').read_text().strip() == '0'
    spec = importlib.util.spec_from_file_location('second_reduction', package / 'check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()
    def read(path):
        return json.loads(path.read_text())
    run_sha = sha(output / 'RUN.json')
    run = read(output / 'RUN.json')
    assert run['status'] == 'PASS'
    library, _, provenance = checker.validate(previous / '_build/prerequisites', previous / '_build/cloud-second', package / '_build/prerequisites/Erdos85ThreeHighPilotDeficientU369R11Certificate.olean')
    assert run['provenance'] == provenance
    dependency = run['dependencies']
    assert dependency['exit_code'] == 0 and dependency['command'] == ['lake', 'build', *library]
    assert dependency['log_sha256'] == sha(output / 'dependencies.log')
    imported = {'Proofs.' + Path(name).stem for name in provenance['imported_object_sha256'] if '/Proofs/' in name}
    imported.add('Proofs.' + provenance['second_certificate_module'])
    assert not imported & set(dependency['command'])
    e = run['result']
    assert e['status'] == 'PASS' and e['exit_code'] == 0
    assert read(output / 'Deficient1552.run.json') == e
    assert sha(package / 'Deficient1552.lean') == e['source_sha256']
    for suffix, key in [('.lean', 'source_sha256'), ('.log', 'log_sha256'), ('.olean', 'olean_sha256')]:
        assert sha(output / ('Deficient1552' + suffix)) == e[key]
    recorded = Path('/workspace') / output.relative_to(repo)
    assert e['command'] == ['lean', '-R', str(recorded), '-o', str(recorded / 'Deficient1552.olean'), str(recorded / 'Deficient1552.lean')]
    log = (output / 'Deficient1552.log').read_text()
    assert 'sorry' not in log.lower()
    reports = [{'theorem': n, 'axioms': [x.strip() for x in (ax or '').split(',') if x.strip()]} for n, ax in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", log)]
    names = ['DeficientUStrongAfterTwoPilots.' + n for n in ['pilot_mem', 'remainingPairs_card', 'pilot_input', 'pilot_rejected', 'actual_distinct_witness', 'excluded_of_rejections']]
    assert [r['theorem'] for r in reports] == names
    assert re.findall(r'^#print axioms (\S+)\s*$', (output / 'Deficient1552.lean').read_text(), re.M) == names
    assert reports == e['axiom_exports']
    standard = {'propext', 'Classical.choice', 'Quot.sound'}
    first = 'Erdos85.VariedPilot.DeficientU26R2.rejected._native.native_decide.ax_1_1'
    second = 'Erdos85.VariedPilot.DeficientU369R11.rejected._native.native_decide.ax_1_1'
    for i, report in enumerate(reports):
        assert set(report['axioms']) == standard | ({second} if i == 3 else {first, second} if i >= 4 else set())
    assert sha(output / 'RUN.json') == run_sha
    print(json.dumps({'status': 'PASS', 'job': a.job, 'authoritative_exit': 0,
        'run_sha256': run_sha, 'job_log_sha256': sha(job / 'log'),
        'result': e, 'provenance': provenance,
        'scope': 'Actual deficient witness connected to 1552 remaining pairs; exclusion requires every remaining rejection.'}, indent=2))


if __name__ == '__main__':
    main()
