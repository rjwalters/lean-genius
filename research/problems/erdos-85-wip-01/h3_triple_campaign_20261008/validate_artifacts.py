"""Read-only artifact validation component, not a campaign acceptance decision.

No subprocesses, Lean execution, retries, or claim mutations. The host collector
must separately establish terminal execution, source/image/toolchain/cache
provenance and resource limits before promoting a result to AUDITED_PASS.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re

import common

STAGES = ('Inputs', 'Membership', 'Certificate', 'Consumer')
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = re.compile(
    r"'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique)


def regular(root, name):
    """Evidence must stay in its retained directory; no symlink substitution."""
    p = root / name
    require(p.is_file() and not p.is_symlink(), 'Missing or linked artifact: ' + name)
    require(p.resolve().parent == root.resolve(), 'Artifact escapes bundle')
    return p


def reports(log):
    require('sorry' not in log.lower(), 'Sorry in compiler log')
    require(re.search(r'\berror:', log, re.I) is None, 'Compiler error in log')
    matches = list(REPORT.finditer(log))
    # Anything resembling a report that failed parsing must not disappear.
    require(len(matches) == log.count('depends on axioms:') +
            log.count('does not depend on any axioms'), 'Malformed axiom report')
    result = []
    for m in matches:
        axioms = [s.strip() for s in (m[2] or '').split(',') if s.strip()]
        require(len(axioms) == len(set(axioms)), 'Duplicate axiom')
        result.append({'theorem': m[1], 'axioms': axioms})
    require(len(result) == len({r['theorem'] for r in result}), 'Duplicate theorem report')
    return result


def exports(case, stage):
    suffixes = {'Inputs': [], 'Membership': ['member', 'input_identity'],
                'Certificate': ['rejected'],
                'Consumer': ['representative_rejected', 'no_joint']}[stage]
    return [case['namespace'] + '.' + s for s in suffixes]


def command(case, stage, recorded_root):
    """Fixed layout shared with the future worker; no worker-selected commands."""
    root = PurePosixPath(recorded_root)
    require(root.is_absolute() and '..' not in root.parts, 'Invalid recorded root')
    name = case['module_prefix'] + stage
    library = stage in ('Inputs', 'Certificate')
    source_root = root / 'source-root' if library else root / case['id']
    source = source_root / 'Proofs' / (name + '.lean') if library else source_root / (name + '.lean')
    obj = root / 'library/Proofs' / (name + '.olean') if library else source_root / (name + '.olean')
    return ['lean', '-R', str(source_root), '-o', str(obj), str(source)]


def validate_stage(directory, case, stage, entry, recorded_root):
    name = case['module_prefix'] + stage
    require(entry['module'] == name and entry['stage'] == stage and
            entry['case_id'] == case['id'], 'Wrong module, stage or case')
    require(type(entry['exit_code']) is int and entry['exit_code'] == 0,
            'Nonzero or invalid compiler exit')
    require(entry.get('certificate_substitution', False) is False,
            'Bridge substitution is not a production certificate')
    require(entry['command'] == command(case, stage, recorded_root), 'Wrong compiler command')
    for metric in ('elapsed_seconds', 'user_cpu_seconds', 'system_cpu_seconds', 'max_rss_kib'):
        value = entry[metric]
        require(type(value) in (int, float) and math.isfinite(value) and value >= 0,
                'Invalid metric: ' + metric)
    expected = common.sources(case)[name + '.lean'].encode()
    require(hashlib.sha256(expected).hexdigest() == case['source_sha256'][name + '.lean'],
            'Generator does not match manifest')
    source = regular(directory, name + '.lean')
    require(source.read_bytes() == expected, 'Changed generated source')
    for extension, key in (('.lean', 'source_sha256'), ('.log', 'log_sha256'), ('.olean', 'olean_sha256')):
        p = regular(directory, name + extension)
        require(digest(p) == entry[key], 'Changed artifact: ' + p.name)
        if extension == '.olean':
            require(p.stat().st_size > 0, 'Empty Lean object')
    parsed = reports(regular(directory, name + '.log').read_text())
    require([r['theorem'] for r in parsed] == exports(case, stage), 'Wrong export inventory')
    require(parsed == entry['axiom_exports'], 'Recorded axioms differ from raw log')
    native = case['namespace'] + '.rejected._native.native_decide.ax_1_1'
    for report in parsed:
        actual = set(report['axioms'])
        require(actual <= STANDARD if stage == 'Membership' else actual == STANDARD | {native},
                'Wrong trust set: ' + report['theorem'])
    require(read(regular(directory, name + '.run.json')) == entry, 'Individual receipt differs')
    return {'stage': stage, 'module': name, 'source_sha256': entry['source_sha256'],
            'olean_sha256': entry['olean_sha256'], 'log_sha256': entry['log_sha256'],
            'axiom_exports': parsed}


def validate_bundle(manifest_path, manifest_sha, case_id, attempt, recorded_root,
                    certificate_only=False, preflight_only=False):
    require(not (certificate_only and preflight_only), 'Choose one validation scope')
    require(digest(manifest_path) == manifest_sha, 'Manifest hash mismatch')
    manifest = read(manifest_path)
    require(manifest['schema'] == 'erdos85-h3-triple-manifest-v1', 'Wrong manifest schema')
    for name in ('common.py', 'manifest.py'):
        require(digest(common.PACKAGE / name) == manifest['generator_sha256'][name],
                'Generator pin changed: ' + name)
    candidates = [c for c in manifest['cases'] if c['id'] == case_id]
    require(len(candidates) == 1, 'Unknown or duplicate case')
    case = candidates[0]
    require(case['state'] == 'PENDING', 'Prior credits require their own audit path')
    run_path = regular(attempt, 'RUN.json')
    before = digest(run_path)
    run = read(run_path)
    schema = 'erdos85-h3-triple-preflight-v1' if preflight_only else 'erdos85-h3-triple-receipt-v1'
    require(run['schema'] == schema, 'Wrong receipt schema')
    require(run['production_native_search'] is (not preflight_only), 'Wrong native-search scope')
    require(run['manifest_sha256'] == manifest_sha and run['case_id'] == case_id,
            'Wrong attempt manifest or case')
    require(re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{7,127}', run['attempt_id']) is not None,
            'Invalid attempt ID')
    require(run['recorded_root'] == recorded_root, 'Wrong attempt root')
    entries = run['results']
    needed = STAGES[:2] if preflight_only else STAGES[:3] if certificate_only else STAGES
    require(len(entries) in (3, 4) if certificate_only else len(entries) == len(needed),
            'Incomplete or extra module inventory')
    require([e['stage'] for e in entries] == list(STAGES[:len(entries)]),
            'Wrong module order or duplicate stage')
    directory = attempt / case_id
    require(directory.is_dir() and not directory.is_symlink(), 'Missing or linked case directory')
    artifacts = [regular(directory, case['module_prefix'] + stage + suffix)
                 for stage in needed for suffix in ('.lean', '.log', '.olean', '.run.json')]
    snapshot = {p: digest(p) for p in artifacts}
    checked = [validate_stage(directory, case, stage, entry, recorded_root)
               for stage, entry in zip(needed, entries)]
    require(all(not p.is_symlink() and digest(p) == sha for p, sha in snapshot.items()),
            'Artifacts changed during validation')
    require(digest(run_path) == before, 'Receipt changed during validation')
    return {'status': 'PREFLIGHT_ARTIFACTS_VALID' if preflight_only else
                     'CERTIFICATE_ARTIFACTS_VALID' if certificate_only else 'ARTIFACTS_VALID',
            'case_id': case_id, 'attempt_id': run['attempt_id'], 'manifest_sha256': manifest_sha,
            'run_sha256': before, 'results': checked, 'campaign_credit': False,
            'retry_authorized': False,
            'scope': 'Artifact component only. Requires independent host execution/provenance audit; '
                     'does not establish terminal state, authorize retry, or credit the campaign.'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--case', required=True)
    p.add_argument('--attempt', type=Path, required=True)
    p.add_argument('--recorded-root', required=True)
    scope = p.add_mutually_exclusive_group()
    scope.add_argument('--certificate-only', action='store_true')
    scope.add_argument('--preflight-only', action='store_true')
    a = p.parse_args()
    print(json.dumps(validate_bundle(a.manifest, a.manifest_sha256, a.case, a.attempt,
                                    a.recorded_root, a.certificate_only, a.preflight_only), indent=2))


if __name__ == '__main__':
    main()
