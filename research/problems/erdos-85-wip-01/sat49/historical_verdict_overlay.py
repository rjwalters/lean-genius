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
