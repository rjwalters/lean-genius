"""Cloud bridge canary: exact campaign inputs/membership/consumer, old native proofs.

This is NOT a production native-search receipt. Certificate source is explicitly
substituted to import an independently audited prior rejection. All compiled
objects are written to a private complete library copy, never the shared cache.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
import common
import manifest as inventory


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


previous = load('canary_full', common.RESEARCH / 'h3_u1r15_census_reduction_20261008/check.py')
deficient = load('canary_deficient', common.RESEARCH / 'h3_varied_pilot_20261008/check_preflight.py')
timing = previous.timing
require, digest = previous.require, timing.digest
CASES = ['full-u003-r03', 'deficient-u026-r02']


def read(path):
    return json.loads(path.read_text())


def verify_manifest(expected):
    path = common.PACKAGE / 'MANIFEST.json'
    require(digest(path) == expected, 'Manifest hash mismatch')
    m = read(path)
    for name, sha in m['generator_sha256'].items():
        require(digest(common.PACKAGE / name) == sha, 'Generator changed')
    for section in ['source_inputs_sha256', 'prerequisite_sources_sha256']:
        for name, sha in m[section].items():
            p = common.REPO / name
            require((digest(p) if p.exists() else None) == sha, 'Source snapshot changed: ' + name)
    return m


def validate(m, full, deficient_base, old_objects):
    _, full_audit = previous.census(full / 'base', full / 'final', m['base_receipts']['full_final'])
    deficient.validate_base(deficient_base)
    copies, cases = [], []
    for ident in CASES:
        c, = [r for r in m['cases'] if r['id'] == ident]
        require(c['state'] == 'REUSED_PASS', 'Canary must use an audited prior credit')
        credit = c['credit']
        directory = (common.REPO / credit['receipt']).parent
        run, audit = read(directory / 'RUN.json'), read(directory / 'AUDIT.json')
        require(run['status'] == audit['status'] == 'PASS'
                and digest(directory / 'RUN.json') == credit['receipt_sha256'] == audit['run_sha256']
                and digest(directory / 'AUDIT.json') == credit['audit_sha256'], 'Prior evidence changed')
        require((run['case']['branch'], run['case']['u_index'], run['case']['r_index']) == (c['branch'], c['u_index'], c['r_index']), 'Prior case mismatch')
        for e in run['results']:
            name = e['module']
            require(e['status'] == 'PASS' and e['exit_code'] == 0, 'Failed prior module')
            require(digest(directory / (name + '.lean')) == e['source_sha256']
                    and digest(directory / (name + '.log')) == e['log_sha256'], 'Prior source/log changed')
            if name.endswith('Inputs') or name.endswith('Certificate'):
                source = old_objects / (name + '.olean')
                require(digest(source) == e['olean_sha256'], 'Prior object changed: ' + name)
                copies.append((source, name, e['olean_sha256']))
        require(common.source_hashes(c) == c['source_sha256'], 'Generated source hashes changed')
        cases.append((c, run['case']['namespace']))
    return full_audit, copies, cases


def bridge_source(c, old_namespace):
    return f'''import Proofs.{c['credit']['certificate_module']}
import Proofs.{c['module_prefix']}Inputs
namespace {c['namespace']}
open Erdos85
theorem rejected : threeHighNativePairSearch U R = false := by
  exact {old_namespace}.rejected
end {c['namespace']}
#print axioms {c['namespace']}.rejected
'''


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--full-prerequisites', type=Path, required=True)
    p.add_argument('--deficient-base', type=Path, required=True)
    p.add_argument('--old-objects', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    require(Path('/.dockerenv').exists() and Path('Proofs').is_dir(), 'Run only inside cloud Docker from proofs')
    full, deficient_base, old_objects, output = [v.resolve() for v in (a.full_prerequisites, a.deficient_base, a.old_objects, a.output)]
    m = verify_manifest(a.manifest_sha256)
    prerequisite_audit, copies, cases = validate(m, full, deficient_base, old_objects)
    output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    receipt = {'schema': 'erdos85-h3-triple-bridge-canary-v1', 'status': 'RUNNING',
               'production_native_search': False, 'manifest_sha256': a.manifest_sha256,
               'full_prerequisite_audit': prerequisite_audit, 'results': [],
               'source_sha256': digest(Path(__file__)),
               'scope': 'Generated source bridge canary with substituted prior proofs; no new native search or production-worker claim.'}

    def save():
        tmp = output / 'RUN.json.tmp'
        tmp.write_text(json.dumps(receipt, indent=2) + '\n')
        tmp.replace(output / 'RUN.json')

    save()
    library = ['Proofs.Erdos85ThreeHighNativePairSearch', 'Proofs.Erdos85ThreeBlockCompactCodes', 'Proofs.Erdos85ThreeHighSecondaryOrbitTable']
    receipt['dependencies'] = timing.run(['lake', 'build', *library], output / 'dependencies.log', env)
    save()
    if receipt['dependencies']['exit_code']:
        receipt['status'] = 'DEPENDENCY_FAILURE'
        save()
        return 1
    # A complete private Proofs namespace avoids partial-root shadowing and
    # prevents the substituted certificate objects from entering production cache.
    private_library = output / 'library'
    subprocess.run(['cp', '-a', '--reflink=auto', str(Path('.lake/build/lib/lean').resolve()), str(private_library)], check=True)
    for src, name, sha in copies:
        dst = private_library / 'Proofs' / (name + '.olean')
        if dst.exists():
            require(digest(dst) == sha, 'Different imported private object')
        else:
            shutil.copyfile(src, dst)
        require(digest(dst) == sha, 'Imported object copy mismatch')
    source_root = output / 'source-root'
    (source_root / 'Proofs').mkdir(parents=True)
    for c, old_namespace in cases:
        case_output = output / c['id']
        case_output.mkdir()
        texts = common.sources(c)
        original_certificate = texts[c['module_prefix'] + 'Certificate.lean']
        texts[c['module_prefix'] + 'Certificate.lean'] = bridge_source(c, old_namespace)
        imports = [str(private_library), str(case_output)]
        imports.extend([str(full / 'final'), str(full / 'base')] if c['branch'] == 'full' else [str(deficient_base)])
        env['LEAN_PATH'] = os.pathsep.join(imports + [os.environ.get('LEAN_PATH', '')])
        for suffix in ['Inputs', 'Membership', 'Certificate', 'Consumer']:
            name = c['module_prefix'] + suffix
            retained = case_output / (name + '.lean')
            retained.write_text(texts[name + '.lean'])
            is_library = suffix in ['Inputs', 'Certificate']
            source = source_root / 'Proofs' / retained.name if is_library else retained
            if is_library:
                shutil.copyfile(retained, source)
            obj = private_library / 'Proofs' / (name + '.olean') if is_library else case_output / (name + '.olean')
            root = source_root if is_library else case_output
            log = case_output / (name + '.log')
            result = timing.run(['lean', '-R', str(root), '-o', str(obj), str(source)], log, env)
            reports = timing.reports(log.read_text())
            wanted = ([] if suffix == 'Inputs' else [c['namespace'] + '.member', c['namespace'] + '.input_identity'] if suffix == 'Membership'
                      else [c['namespace'] + '.rejected'] if suffix == 'Certificate'
                      else [c['namespace'] + '.representative_rejected', c['namespace'] + '.no_joint'])
            passed = (result['exit_code'] == 0 and obj.is_file() and 'sorry' not in log.read_text().lower()
                      and [r['theorem'] for r in reports] == wanted)
            for report in reports:
                passed = passed and (set(report['axioms']) <= timing.STANDARD if suffix == 'Membership'
                    else set(report['axioms']) == timing.STANDARD | {old_namespace + '.rejected._native.native_decide.ax_1_1'})
            if suffix != 'Certificate':
                passed = passed and digest(retained) == c['source_sha256'][retained.name]
            if passed and is_library:
                shutil.copyfile(obj, case_output / obj.name)
            result.update(case_id=c['id'], module=name, stage=suffix, status='PASS' if passed else 'FAIL',
                          source_sha256=digest(retained), olean_sha256=digest(obj) if obj.exists() else None,
                          axiom_exports=reports, certificate_substitution=suffix == 'Certificate')
            if suffix == 'Certificate':
                result['production_source_sha256_not_executed'] = hashlib.sha256(original_certificate.encode()).hexdigest()
                result['prior_native_namespace'] = old_namespace
            (case_output / (name + '.run.json')).write_text(json.dumps(result, indent=2) + '\n')
            receipt['results'].append(result)
            save()
            print(json.dumps({'case': c['id'], 'stage': suffix, 'status': result['status']}), flush=True)
            if not passed:
                receipt['status'] = 'MODULE_FAILURE'
                save()
                return 1
    require(verify_manifest(a.manifest_sha256) == m, 'Manifest changed')
    require(validate(m, full, deficient_base, old_objects) == (prerequisite_audit, copies, cases), 'Prerequisites changed')
    receipt['status'] = 'BRIDGE_CANARY_PASS'
    save()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
