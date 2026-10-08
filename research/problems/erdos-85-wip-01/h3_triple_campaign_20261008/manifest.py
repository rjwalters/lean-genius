"""Reconstruct the exact triple census and credit independently audited pilots."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import common

CREDITS = [
    ('full', 1, 15, 'h3_cloud_u1r15_20261008/split-evidence', 'b1dd1f5ec0a48fb8e5261b23a3715ff9942edb596bbe7ce0eacd1673a3b17b21', 'h3_u1r15_census_reduction_20261008/evidence'),
    ('full', 3, 3, 'h3_varied_pilot_20261008/FullU3R3-evidence', '1a59f0543cf7ee4ddf31c88a9efd2a15585310a14d333f6281e8abce91eb43d0', 'h3_u1r15_census_reduction_20261008/evidence'),
    ('deficient', 26, 2, 'h3_varied_pilot_20261008/DeficientU26R2-evidence', 'c084a76d8c05199564a29058ae256b205d5d7d94fa9f4dde7bf77a3b2117ee4c', 'h3_varied_pilot_20261008/preflight-evidence'),
    ('deficient', 369, 11, 'h3_varied_pilot_20261008/DeficientU369R11-evidence', '90b9321318d9399384dc04cd63bcd94c2fb97dba662e7a572424e0aeec587c3b', 'h3_varied_pilot_20261008/preflight-evidence'),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def credit(branch, u, r, directory, receipt_sha, identity):
    directory, identity = common.RESEARCH / directory, common.RESEARCH / identity
    run, audit = read(directory / 'RUN.json'), read(directory / 'AUDIT.json')
    if not (run['status'] == audit['status'] == 'PASS' and sha(directory / 'RUN.json') == receipt_sha == audit['run_sha256']):
        raise ValueError('Changed or unaudited pilot: ' + str(directory))
    binding = read(identity / 'AUDIT.json')
    if binding['status'] != 'PASS' or binding['run_sha256'] != sha(identity / 'RUN.json'):
        raise ValueError('Changed identity evidence')
    if 'case' in run:
        c = run['case']
        if (c['branch'], c['u_index'], c['r_index']) != (branch, u, r):
            raise ValueError('Credit case mismatch')
    certificate, = [e for e in run['results'] if e['module'].endswith('Certificate')]
    consumer, = [e for e in run['results'] if any(r['theorem'].endswith('.no_joint') for r in e.get('axiom_exports', []))]
    for e in run['results']:
        if e['status'] != 'PASS' or e['exit_code'] != 0:
            raise ValueError('Failed pilot module')
        for suffix, key in [('.lean', 'source_sha256'), ('.log', 'log_sha256')]:
            if sha(directory / (e['module'] + suffix)) != e[key]:
                raise ValueError('Changed pilot artifact')
    return {'receipt': str((directory / 'RUN.json').relative_to(common.REPO)), 'receipt_sha256': receipt_sha,
            'audit_sha256': sha(directory / 'AUDIT.json'),
            'identity_audit': str((identity / 'AUDIT.json').relative_to(common.REPO)),
            'identity_audit_sha256': sha(identity / 'AUDIT.json'),
            'certificate_module': certificate['module'], 'certificate_object_sha256': certificate['olean_sha256'],
            'consumer_module': consumer['module'], 'consumer_object_sha256': consumer['olean_sha256'],
            'certificate_wall_seconds': certificate['elapsed_seconds'],
            'certificate_cpu_seconds': certificate['user_cpu_seconds'] + certificate['system_cpu_seconds'],
            'certificate_max_rss_kib': certificate['max_rss_kib']}



def prerequisite_sources():
    path = common.RESEARCH / 'h3_strong_final_census_20261008/check.py'
    spec = importlib.util.spec_from_file_location('campaign_census', path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    base, final, library = m.plan()
    deficient, _, deficient_library = m.census.plan('deficient')
    paths = {p for _, p in base + final + deficient}
    pending = list(set(library) | set(deficient_library) | {'Proofs.Erdos85ThreeHighNativePairSearch', 'Proofs.Erdos85ThreeBlockCompactCodes', 'Proofs.Erdos85ThreeHighSecondaryOrbitTable'})
    seen = set()
    while pending:
        module = pending.pop()
        if not module.startswith('Proofs.') or module in seen:
            continue
        seen.add(module)
        source = common.REPO / 'proofs' / (module.replace('.', '/') + '.lean')
        if not source.is_file():
            raise ValueError('Missing transitive library source: ' + module)
        paths.add(source)
        pending.extend(m.census.imports(source))
    paths.update(common.REPO / 'proofs' / n for n in ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json'])
    return {str(p.relative_to(common.REPO)): sha(p) if p.exists() else None for p in sorted(paths)}


def build(final_receipt=None):
    pairs, tables, secondary, provenance = common.inventory()
    credits = list(CREDITS)
    if final_receipt:
        credits.append(('full', 54, 20, 'h3_varied_pilot_20261008/FullU54R20-evidence', final_receipt,
                        'h3_u1r15_census_reduction_20261008/evidence'))
    reused = {(b, u, r): credit(b, u, r, directory, expected, identity)
              for b, u, r, directory, expected, identity in credits}
    rows = []
    for branch in ('full', 'deficient'):
        for u, r in pairs[branch]:
            c = common.case(branch, u, r, tables[branch][u], secondary[r])
            c['source_sha256'] = common.source_hashes(c)
            c['state'] = 'REUSED_PASS' if (branch, u, r) in reused else 'PENDING'
            if c['state'] == 'REUSED_PASS':
                c['credit'] = reused[(branch, u, r)]
            rows.append(c)
    assert len(rows) == 1815 and len({r['id'] for r in rows}) == 1815
    assert len(reused) == sum(r['state'] == 'REUSED_PASS' for r in rows)
    return {'schema': 'erdos85-h3-triple-manifest-v1', 'status': 'PREPARED_NOT_LAUNCHED',
            'unit': 'complete_u_r_pair', 'census_counts': {b: len(v) for b, v in pairs.items()},
            'compute_counts': {'total': len(rows), 'reused': len(reused), 'pending': len(rows) - len(reused)},
            'source_inputs_sha256': provenance,
            'prerequisite_sources_sha256': prerequisite_sources(),
            'generator_sha256': {p.name: sha(p) for p in [common.PACKAGE / 'common.py', common.PACKAGE / 'manifest.py']},
            'base_receipts': {'full': '9924e45dfa932bae6af3607eb7de97e4b77d590366bf8d4bb9eaaf8de480236f',
                              'full_final': 'dd262a3d974d3da91d5365dd88d7668183f55cb6083a5dca803588ba517217cb',
                              'deficient': '190d7e37c814bd8a7eea54e6ad1bbcba73e092e6e0d77deddc717bab098bfecc'},
            'cases': rows,
            'scope': 'Compute queue plus audited reuse; does not claim a Lean aggregation or stratum exclusion.'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--write', action='store_true')
    p.add_argument('--full54-receipt-sha256')
    p.add_argument('--emit-case')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    manifest = build(a.full54_receipt_sha256)
    data = json.dumps(manifest, indent=2, sort_keys=True) + '\n'
    if a.write:
        (common.PACKAGE / 'MANIFEST.json').write_text(data)
    if a.emit_case:
        matches = [c for c in manifest['cases'] if c['id'] == a.emit_case]
        if len(matches) != 1 or a.output is None:
            p.error('one known --emit-case and a fresh --output are required')
        a.output.mkdir(parents=True, exist_ok=False)
        for name, source in common.sources(matches[0]).items():
            (a.output / name).write_text(source)
    print(json.dumps({'status': manifest['status'], 'counts': manifest['compute_counts'],
                      'manifest_sha256': hashlib.sha256(data.encode()).hexdigest()}))


if __name__ == '__main__':
    main()
