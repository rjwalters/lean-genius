"""Validate retained historical H1 verdict evidence, without replaying proofs.

The exact overlay, audit and native comparison snapshots must all be committed
by the caller. This verifies their joins; it does not rehash old proof payloads
or assert that inherited drat-trim reports are new certificates.
"""
import hashlib
import json
from pathlib import Path
import re


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def unique(rows, key):
    result = {row[key]: row for row in rows}
    if len(result) != len(rows):
        raise ValueError(f'Duplicate historical {key}')
    return result


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_overlay(path, expected_sha256, frozen_raw):
    raw = path.read_bytes()
    require(digest(raw) == expected_sha256, 'Historical overlay hash mismatch')
    overlay = json.loads(raw)
    if overlay.get('schema') == 'erdos85-h1-historical-verdict-overlay-v2':
        return load_manifest_joined(path, raw, overlay, frozen_raw)
    require(overlay.get('schema') == 'erdos85-h1-historical-verdict-overlay-v1', 'Historical overlay schema')
    require(overlay['frozen_manifest_sha256'] == digest(frozen_raw), 'Historical frozen manifest mismatch')
    captured = [(path, raw)]
    dependencies = {}
    for name in ('audit', 'comparison'):
        ref = overlay['sources'][name]
        dependency = (path.parent / ref['path']).resolve()
        data = dependency.read_bytes()
        require(digest(data) == ref['sha256'], f'Historical {name} snapshot mismatch')
        captured.append((dependency, data)); dependencies[name] = json.loads(data)
    audit, comparison = dependencies['audit'], dependencies['comparison']
    require(audit['manifest_sha256'] == digest(frozen_raw), 'Audit manifest mismatch')
    require(audit['comparison_results_sha256'] == overlay['sources']['comparison']['sha256'], 'Audit/comparison mismatch')
    require(overlay['audit_sha256'] == overlay['sources']['audit']['sha256'], 'Overlay/audit mismatch')
    frozen = unique(json.loads(frozen_raw)['rows'], 'tag')
    audited = unique(audit['results'], 'tag')
    compared = unique(comparison['results'], 'tag')
    rows = unique(overlay['rows'], 'id')
    eligible = {r['tag'] for r in audited.values() if r['paired_verified'] and r['verified_modes'] == ['MONO']}
    require(overlay['count'] == len(rows) == len(eligible) == 95, 'Expected exact 95 paired MONO cases')
    require({r['tag'] for r in rows.values()} == eligible, 'Historical eligible set mismatch')
    pairs = [(i,j) for i in range(8) for j in range(i+1,8) if j != (i^1)]
    for name, row in rows.items():
        tag = row['tag']; original = frozen[tag]; a = audited[tag]; c = compared[tag]
        require(name == 'h1_' + tag == original['id'], 'Historical case identity mismatch')
        require(row['profile'] == a['profile'] == int(c['profile']) == int(original['profile']), 'Historical profile mismatch')
        sha = row['cnf_sha256']
        require(re.fullmatch('[0-9a-f]{64}', sha) is not None, 'Historical CNF hash format')
        require(sha == a['canonical_sha256'] == c['canonical_sha256'], 'Historical CNF join mismatch')
        require(c['status'] == 'BYTE_MATCH', 'Native comparison was not a byte match')
        receipt = c['materialization_receipt']
        require(receipt['status'] == 'materialized' and receipt['container_absent'] is True, 'Native materialization incomplete')
        require(receipt['id'] == name and receipt['manifest_sha256'] == digest(frozen_raw)
                and receipt['cnf_sha256'] == sha and receipt['profile'] == row['profile'], 'Native receipt identity mismatch')
        require(receipt['emit']['returncode'] == receipt['check']['returncode'] == 0, 'Native emitter/check failed')
        require(row['historical_status'] == 'historical_verified_unsat' and row['proof_replayed'] is False, 'Historical evidence scope changed')
        table = [[list(pair),value] for pair,value in zip(pairs,original['table_values'],strict=True) if value]
        require(hashlib.sha1(json.dumps(table).encode()).hexdigest()[:16] == tag, 'Historical table/tag mismatch')
        require(bool(row['evidence']), 'Historical row has no paired evidence')
        for evidence in row['evidence']:
            text = evidence['verdict']; fields, encoded_table = text.strip().split('table:',1)
            tokens = fields.split()
            require(len(tokens) in (6,7) and tokens[:2] == [tag,'UNSAT']
                    and re.fullmatch(r'[0-9]+(?:\.[0-9]+)?s',tokens[2]) is not None
                    and tokens[3:6] == ['drat:VERIFIED','mode:MONO','arm:v2'], 'Historical verdict framing/status mismatch')
            if len(tokens) == 7:
                require(tokens[6] == 'profile:' + original['family'], 'Historical verdict profile mismatch')
            require(sorted(json.loads(encoded_table)) == table, 'Historical verdict table mismatch')
            require(evidence['mode'] == 'MONO' and digest(text.encode()) == evidence['verdict_sha256'], 'Historical verdict digest/mode mismatch')
            matches = [b for b in c['baselines'] if b['path'] == evidence['cnf_path']]
            require(len(matches) == 1, 'Historical baseline absent or duplicated')
            baseline = matches[0]
            require(baseline['sha256'] == sha and baseline['verified_verdict_and_table'] is True
                    and baseline['verdict_path'] == evidence['verdict_path'] and baseline['verdict'] == text,
                    'Historical comparison/verdict join mismatch')
            matches = [b for b in a['matches'] if b['path'] == evidence['cnf_path']]
            require(len(matches) == 1 and matches[0]['verified_verdict_and_table'] is True
                    and matches[0]['mode'] == 'MONO' and matches[0]['verdict_sha256'] == evidence['verdict_sha256'],
                    'Historical audit/verdict join mismatch')
    return list(rows.values()), captured


BASE95_SHA256 = '80fd7a2653f66912c45b8099d83c73bfbdc6005f90efa935d4d9a9f1ca298d98'
MANIFEST_JOINED_TAG = '4ee646ca0ec3e2f0'


def load_manifest_joined(path, raw, overlay, frozen_raw):
    """Explicit second format for the single review-2014 historical case.

    The old 95-row parser is called unchanged. The short verdict here obtains
    its table identity from the separately retained local manifest and its
    check report from the paired drat-trim log; neither is a new proof replay.
    """
    require(overlay['count'] == 96 and overlay['frozen_manifest_sha256'] == digest(frozen_raw),
            'Expected reviewed 96-case wrapper and frozen manifest')
    base = overlay['base_overlay']
    require(base['sha256'] == BASE95_SHA256, '96 wrapper must retain the exact reviewed 95 base')
    base_path = (path.parent / base['path']).resolve()
    rows, captured = load_overlay(base_path, base['sha256'], frozen_raw)
    require(len(rows) == 95, '96 wrapper base cardinality mismatch')
    captured = [(path, raw), *captured]
    data = {}
    for name in ('audit', 'comparison'):
        ref = overlay['extra_sources'][name]
        source = (path.parent / ref['path']).resolve(); source_raw = source.read_bytes()
        require(digest(source_raw) == ref['sha256'], f'Extra {name} snapshot mismatch')
        captured.append((source, source_raw)); data[name] = json.loads(source_raw)
    audit, comparison = data['audit'], data['comparison']
    row = overlay['extra_case']; tag = MANIFEST_JOINED_TAG; name = 'h1_' + tag
    require(row['tag'] == audit['tag'] == comparison['tag'] == tag and row['id'] == name,
            'Only the reviewed manifest-joined singleton is supported')
    require(name not in {r['id'] for r in rows}, 'Duplicate extra historical case')
    original = unique(json.loads(frozen_raw)['rows'], 'tag')[tag]
    require(row['profile'] == audit['profile'] == int(comparison['profile']) == int(original['profile']) == 1,
            'Extra profile mismatch')
    require(row['evidence_format'] == 'manifest_joined_mono' and row['historical_status'] == 'historical_verified_unsat'
            and row['proof_replayed'] is False and audit['proof_replayed'] is False, 'Extra evidence scope mismatch')
    sha = row['cnf_sha256']; receipt = comparison['materialization_receipt']
    require(re.fullmatch('[0-9a-f]{64}', sha) is not None and
            sha == audit['canonical_sha256'] == comparison['canonical_sha256'] == receipt['cnf_sha256'],
            'Extra canonical identity mismatch')
    require(comparison['status'] == 'BYTE_MATCH' and receipt['status'] == 'materialized'
            and receipt['container_absent'] is True and receipt['emit']['returncode'] == receipt['check']['returncode'] == 0,
            'Extra native generation/check incomplete')
    require(receipt['id'] == name and receipt['tag'] == tag and receipt['profile'] == 1
            and receipt['manifest_sha256'] == audit['manifest_sha256'] == digest(frozen_raw), 'Extra native/frozen identity mismatch')
    require((receipt['variables'], receipt['clauses']) == (audit['variables'], audit['clauses'])
            and receipt['cnf_bytes'] == comparison['canonical_bytes'] == receipt['emit']['stdout_bytes'],
            'Extra native dimensions mismatch')
    pairs = [(i,j) for i in range(8) for j in range(i+1,8) if j != (i^1)]
    table = [[list(pair),value] for pair,value in zip(pairs,original['table_values'],strict=True) if value]
    require(hashlib.sha1(json.dumps(table).encode()).hexdigest()[:16] == tag
            and digest((json.dumps(table)+'\n').encode()) == receipt['table_sha256'], 'Extra table/tag mismatch')
    require(len(row['evidence']) == 1, 'Expected one explicit manifest-joined evidence record')
    evidence = row['evidence'][0]
    metadata = audit['metadata']
    for item in metadata.values():
        require(digest(item['raw'].encode()) == item['sha256'], 'Extra metadata bytes mismatch')
    manifest = metadata[evidence['local_manifest_path']]
    require(manifest['sha256'] == evidence['local_manifest_sha256'], 'Extra local manifest pin mismatch')
    matches = [line.split('\t') for line in manifest['raw'].splitlines() if line.split('\t')[0] == tag]
    require(len(matches) == 1 and len(matches[0]) == 4, 'Extra local manifest row absent/duplicate')
    fields = matches[0]
    require(fields[1] == '1' and fields[2] == original['family']
            and [int(v) for v in fields[3].split()] == original['table_values'], 'Extra local manifest table/profile mismatch')
    verdict = metadata[evidence['verdict_path']]
    require(verdict['sha256'] == evidence['verdict_sha256'] and verdict['raw'] == evidence['verdict'],
            'Extra verdict bytes mismatch')
    pattern = re.escape(tag) + r' UNSAT [0-9]+(?:\.[0-9]+)?s drat:VERIFIED mode:MONO arm:v2 lean-exact:MATCH profile:1'
    require(re.fullmatch(pattern, verdict['raw'].strip()) is not None and evidence['mode'] == 'MONO', 'Extra short verdict framing/status mismatch')
    log = metadata[evidence['trim_log_path']]
    require(log['sha256'] == evidence['trim_log_sha256'], 'Extra trim log pin mismatch')
    require([line.strip() for line in log['raw'].splitlines() if line.startswith('s ')] == ['s VERIFIED'],
            'Extra trim log not uniquely VERIFIED')
    headers = re.findall(r'^c parsing input formula with ([0-9]+) variables and ([0-9]+) clauses$',log['raw'],re.M)
    require(headers == [(str(receipt['variables']),str(receipt['clauses']))], 'Extra trim log dimensions mismatch')
    baselines = [b for b in comparison['baselines'] if b['path'] == evidence['cnf_path']]
    require(len(baselines) == 1 and baselines[0]['sha256'] == sha
            and baselines[0]['bytes'] == receipt['cnf_bytes'] and baselines[0]['verdict_path'] == evidence['verdict_path']
            and baselines[0]['verdict'] == verdict['raw'], 'Extra baseline/verdict mismatch')
    require(audit['local_manifest_table_matches'] is True and audit['paired_verdict_verified_mono'] is True
            and audit['paired_drat_log_verified_matching_header'] is True, 'Extra independent audit did not pass')
    return [*rows, row], captured
