"""Cloud-only connection of two audited deficient native certificates."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import sys
sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent
RESEARCH = PACKAGE.parent
VARIED = RESEARCH / 'h3_varied_pilot_20261008'
PREVIOUS = RESEARCH / 'h3_deficient_pilot_reduction_20261008'
PRIOR_SHA = '368442552377b3438ffeaea3fd291c327b5cfeec9432e94b4b913cfef2bcb0f0'
SECOND_SHA = '90b9321318d9399384dc04cd63bcd94c2fb97dba662e7a572424e0aeec587c3b'
NATIVE_FIRST = 'Erdos85.VariedPilot.DeficientU26R2.rejected._native.native_decide.ax_1_1'
NATIVE_SECOND = 'Erdos85.VariedPilot.DeficientU369R11.rejected._native.native_decide.ax_1_1'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


previous = load('previous_reduction', PREVIOUS / 'check.py')
timing = previous.timing
require, digest = previous.require, timing.digest


def read(path):
    return json.loads(path.read_text())


def validate(prerequisites, prior_build, second_object):
    library, objects, first_sha = previous.validate(prerequisites)
    timing.preflight('DeficientU369R11', VARIED / 'preflight-evidence')
    for directory, wanted in [(PREVIOUS / 'evidence', PRIOR_SHA),
                              (VARIED / 'DeficientU369R11-evidence', SECOND_SHA)]:
        require(digest(directory / 'RUN.json') == wanted, 'Changed audited receipt')
        require(read(directory / 'AUDIT.json')['status'] == 'PASS'
                and read(directory / 'AUDIT.json')['run_sha256'] == wanted,
                'Missing independent audit')
    require(digest(prior_build / 'RUN.json') == PRIOR_SHA, 'Different prior build')
    prior = read(prior_build / 'RUN.json')
    require(prior['status'] == 'PASS' and prior['pilot_receipt_sha256'] == first_sha
            and prior['imported_object_sha256'] == objects, 'Prior prerequisites differ')
    old = prior['result']
    require(old['status'] == 'PASS' and old['exit_code'] == 0
            and read(prior_build / 'Deficient1553.run.json') == old, 'Prior module failed')
    for suffix, key in [('.lean', 'source_sha256'), ('.log', 'log_sha256'), ('.olean', 'olean_sha256')]:
        require(digest(prior_build / ('Deficient1553' + suffix)) == old[key], 'Prior artifact changed')
    require(digest(PREVIOUS / 'Deficient1553.lean') == old['source_sha256'], 'Prior source changed')
    old_recorded = Path(old['command'][2])
    require(old['command'] == ['lean', '-R', str(old_recorded), '-o', str(old_recorded / 'Deficient1553.olean'), str(old_recorded / 'Deficient1553.lean')], 'Prior command changed')
    reports = timing.reports((prior_build / 'Deficient1553.log').read_text())
    require(reports == old['axiom_exports'] and len(reports) == 6, 'Prior export mismatch')
    for i, report in enumerate(reports):
        require(set(report['axioms']) == timing.STANDARD | ({NATIVE_FIRST} if i >= 3 else set()), 'Prior trust set changed')
    require(prior['dependencies']['exit_code'] == 0
            and prior['dependencies']['command'] == ['lake', 'build', *library]
            and digest(prior_build / 'dependencies.log') == prior['dependencies']['log_sha256'], 'Prior dependency mismatch')
    require(digest(prior_build / 'DeficientMembership.olean') == objects['extra/DeficientMembership.olean'], 'Prior membership object changed')
    pilot = VARIED / 'DeficientU369R11-evidence'
    receipt = read(pilot / 'RUN.json')
    require(receipt['status'] == 'PASS', 'Second pilot failed')
    certificate = None
    for e in receipt['results']:
        name = e['module']
        require(e['status'] == 'PASS' and e['exit_code'] == 0, 'Second pilot module failed')
        require(digest(pilot / (name + '.lean')) == e['source_sha256'] == digest(VARIED / (name + '.lean')), 'Pilot source changed')
        require(digest(pilot / (name + '.log')) == e['log_sha256'], 'Pilot log changed')
        if name.endswith('Certificate'):
            certificate = e
            selected = [r for r in timing.reports((pilot / (name + '.log')).read_text()) if r['theorem'] == 'Erdos85.VariedPilot.DeficientU369R11.rejected']
            require(selected == e['axiom_exports'] and len(selected) == 1
                    and set(selected[0]['axioms']) == timing.STANDARD | {NATIVE_SECOND}, 'Second certificate trust mismatch')
    require(certificate is not None and digest(second_object) == certificate['olean_sha256'], 'Second certificate object changed')
    return library, objects, {'prior_receipt_sha256': PRIOR_SHA, 'second_pilot_receipt_sha256': SECOND_SHA,
        'base_receipt_sha256': previous.preflight.BASE_SHA, 'first_pilot_receipt_sha256': first_sha,
        'prior_object_sha256': old['olean_sha256'], 'second_certificate_module': certificate['module'],
        'second_certificate_object_sha256': certificate['olean_sha256'], 'imported_object_sha256': objects}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--prerequisites', type=Path, required=True)
    p.add_argument('--prior-build', type=Path, required=True)
    p.add_argument('--second-object', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    require(Path('/.dockerenv').exists() and Path('Proofs').is_dir(), 'Run only inside cloud Docker from proofs')
    prerequisites, prior_build, second_object, output = [v.resolve() for v in (a.prerequisites, a.prior_build, a.second_object, a.output)]
    library, objects, provenance = validate(prerequisites, prior_build, second_object)
    output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    receipt = {'status': 'RUNNING', 'provenance': provenance,
               'scope': 'Two existing deficient certificates consumed; 1552 rejection hypotheses remain.'}

    def save():
        temp = output / 'RUN.json.tmp'
        temp.write_text(json.dumps(receipt, indent=2) + '\n')
        temp.replace(output / 'RUN.json')

    save()
    imported = {'Proofs.' + Path(name).stem for name in objects if '/Proofs/' in name}
    imported.add('Proofs.' + provenance['second_certificate_module'])
    require(not imported & set(library), 'Refuse to rebuild imported certificates or inputs')
    receipt['dependencies'] = timing.run(['lake', 'build', *library], output / 'dependencies.log', env)
    save()
    if receipt['dependencies']['exit_code']:
        receipt['status'] = 'DEPENDENCY_FAILURE'
        save()
        return 1
    root = Path('.lake/build/lib/lean/Proofs').resolve()
    copies = [(prerequisites / name, root / Path(name).name, sha)
              for name, sha in objects.items() if '/Proofs/' in name]
    copies.append((second_object, root / (provenance['second_certificate_module'] + '.olean'), provenance['second_certificate_object_sha256']))
    for src, dst, sha in copies:
        if dst.exists():
            require(digest(dst) == sha, 'Refuse to replace a different library object')
        else:
            shutil.copyfile(src, dst)
        require(digest(dst) == sha, 'Library object copy mismatch')
    env['LEAN_PATH'] = os.pathsep.join([str(output), str(prior_build), str(prerequisites / 'base'), env.get('LEAN_PATH', '')])
    source = PACKAGE / 'Deficient1552.lean'
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
        expected = timing.STANDARD | ({NATIVE_SECOND} if i == 3 else {NATIVE_FIRST, NATIVE_SECOND} if i >= 4 else set())
        passed = passed and set(report['axioms']) == expected
    require(validate(prerequisites, prior_build, second_object) == (library, objects, provenance), 'Prerequisites changed')
    result.update(module='Deficient1552', status='PASS' if passed else 'FAIL', source_sha256=digest(source),
                  olean_sha256=digest(obj) if obj.is_file() else None, axiom_exports=reports)
    (output / 'Deficient1552.run.json').write_text(json.dumps(result, indent=2) + '\n')
    receipt['result'] = result
    receipt['status'] = result['status']
    save()
    print(json.dumps(receipt), flush=True)
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
