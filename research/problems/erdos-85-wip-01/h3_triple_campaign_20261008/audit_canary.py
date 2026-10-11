"""Read-only audit of the H3 campaign bridge canary, never a production receipt."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
sys.dont_write_bytecode = True


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repository', type=Path, required=True)
    p.add_argument('--job', required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    repo = a.repository.resolve()
    package = repo / 'research/problems/erdos-85-wip-01/h3_triple_campaign_20261008'
    output = a.output.resolve()
    recorded = Path('/workspace') / output.relative_to(repo)
    job = Path('/opt/e85/jobs') / a.job
    assert (job / 'exit').read_text().strip() == '0'
    sys.path.insert(0, str(package))
    spec = importlib.util.spec_from_file_location('bridge_canary', package / 'canary.py')
    c = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(c)
    def read(path):
        return json.loads(path.read_text())
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()
    run_sha = sha(output / 'RUN.json')
    run = read(output / 'RUN.json')
    assert run['schema'] == 'erdos85-h3-triple-bridge-canary-v1'
    assert run['status'] == 'BRIDGE_CANARY_PASS' and run['production_native_search'] is False
    assert run['source_sha256'] == sha(package / 'canary.py')
    m = c.verify_manifest(run['manifest_sha256'])
    full = package.parent / 'h3_u1r15_census_reduction_20261008/_build/prerequisites'
    deficient = package.parent / 'h3_deficient_pilot_reduction_20261008/_build/prerequisites/base'
    prior_audit, copies, cases = c.validate(m, full, deficient, package / '_build/canary-prerequisites')
    assert prior_audit == run['full_prerequisite_audit']
    assert run['dependencies']['exit_code'] == 0
    assert run['dependencies']['command'] == ['lake', 'build', 'Proofs.Erdos85ThreeHighNativePairSearch', 'Proofs.Erdos85ThreeBlockCompactCodes', 'Proofs.Erdos85ThreeHighSecondaryOrbitTable']
    assert run['dependencies']['log_sha256'] == sha(output / 'dependencies.log')
    expected = [(case['id'], stage) for case, _ in cases for stage in ['Inputs', 'Membership', 'Certificate', 'Consumer']]
    assert [(e['case_id'], e['stage']) for e in run['results']] == expected
    source_commit = re.search(r'^\[e85\] commit ([0-9a-f]{40}) ', (job / 'log').read_text(), re.M)[1]
    committed = subprocess.check_output(['git', '-C', str(repo), 'show', source_commit + ':' + str((package / 'canary.py').relative_to(repo))])
    assert hashlib.sha256(committed).hexdigest() == run['source_sha256']
    for e in run['results']:
        case, old_namespace = next((case, old) for case, old in cases if case['id'] == e['case_id'])
        name, stage = e['module'], e['stage']
        retained = output / case['id']
        assert e['status'] == 'PASS' and e['exit_code'] == 0
        assert read(retained / (name + '.run.json')) == e
        for suffix, key in [('.lean', 'source_sha256'), ('.log', 'log_sha256'), ('.olean', 'olean_sha256')]:
            assert sha(retained / (name + suffix)) == e[key]
        generated = c.common.sources(case)[name + '.lean']
        is_library = stage in ['Inputs', 'Certificate']
        if stage == 'Certificate':
            assert e['certificate_substitution'] is True
            assert e['production_source_sha256_not_executed'] == hashlib.sha256(generated.encode()).hexdigest() == case['source_sha256'][name + '.lean']
            assert (retained / (name + '.lean')).read_text() == c.bridge_source(case, old_namespace)
        else:
            assert e['certificate_substitution'] is False
            assert (retained / (name + '.lean')).read_text() == generated
            assert e['source_sha256'] == case['source_sha256'][name + '.lean']
        root = recorded / 'source-root' if is_library else recorded / case['id']
        src = root / 'Proofs' / (name + '.lean') if is_library else root / (name + '.lean')
        obj = recorded / 'library/Proofs' / (name + '.olean') if is_library else root / (name + '.olean')
        assert e['command'] == ['lean', '-R', str(root), '-o', str(obj), str(src)]
        if is_library:
            assert sha(output / 'library/Proofs' / (name + '.olean')) == e['olean_sha256']
            assert sha(output / 'source-root/Proofs' / (name + '.lean')) == e['source_sha256']
            shared = '/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs/' + name + '.olean'
            assert subprocess.run(['sudo', 'test', '-e', shared]).returncode == 1
        log = (retained / (name + '.log')).read_text()
        assert 'sorry' not in log.lower()
        reports = [{'theorem': n, 'axioms': [v.strip() for v in (ax or '').split(',') if v.strip()]} for n, ax in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", log)]
        wanted = ([] if stage == 'Inputs' else [case['namespace'] + '.member', case['namespace'] + '.input_identity'] if stage == 'Membership' else [case['namespace'] + '.rejected'] if stage == 'Certificate' else [case['namespace'] + '.representative_rejected', case['namespace'] + '.no_joint'])
        assert [r['theorem'] for r in reports] == wanted and reports == e['axiom_exports']
        for r in reports:
            if stage == 'Membership':
                assert set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
            else:
                assert set(r['axioms']) == {'propext', 'Classical.choice', 'Quot.sound', old_namespace + '.rejected._native.native_decide.ax_1_1'}
    assert sha(output / 'RUN.json') == run_sha
    print(json.dumps({'status': 'BRIDGE_CANARY_AUDIT_PASS', 'job': a.job, 'execution_commit': source_commit,
        'authoritative_exit': 0, 'run_sha256': run_sha, 'job_log_sha256': sha(job / 'log'),
        'manifest_sha256': run['manifest_sha256'], 'modules': len(run['results']),
        'axiom_reports': sum(len(e['axiom_exports']) for e in run['results']),
        'production_native_search': False, 'shared_campaign_objects_absent': True,
        'scope': 'Exact generated Inputs/Membership/Consumer sources checked for two branches using explicitly substituted old proofs. No production worker or new rejection credit.'}, indent=2))


if __name__ == '__main__':
    main()
