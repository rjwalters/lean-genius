"""Consume the exact reviewed 95-row historical snapshot, without proof replay.

This allowlist supports review2009's 95 rows and review2017's explicit 96th row. Expanding
the historical set requires a new reviewed pin; captured Python is never run.
"""
import hashlib
import json

APPROVED_OVERLAY = '80fd7a2653f66912c45b8099d83c73bfbdc6005f90efa935d4d9a9f1ca298d98'
APPROVED_OVERLAY96 = 'f60a65905e9e1f23896151aad2b51cc87ff3f685ae9a5ce59aeac3c2b530495d'
APPROVED_MANIFEST = 'c10965a5d9473107169badf4996b73da13edc522cf344c4bcdb45e1a05e7d16b'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_reviewed_history(config, snapshots, state, cases, manifest_sha256):
    ref = config.get('historical_overlay')
    if ref is None:
        require(not state.get('historical_evidence') and not state.get('historical_skipped'),
                'Historical evidence without configured overlay')
        return {}
    require(ref['sha256'] in {APPROVED_OVERLAY, APPROVED_OVERLAY96}, 'Historical overlay is not the reviewed 95/96-row snapshot')
    require(manifest_sha256 == APPROVED_MANIFEST, 'Historical frozen manifest is not approved')

    def snapshot(sha):
        require(sha in snapshots, 'Missing historical snapshot')
        raw = snapshots[sha]
        require(hashlib.sha256(raw).hexdigest() == sha, 'Historical snapshot bytes mismatch')
        return json.loads(raw)

    overlay = snapshot(APPROVED_OVERLAY)
    # The approved overlay bytes pin these two independent-review inputs.
    audit_sha = overlay['sources']['audit']['sha256']
    comparison_sha = overlay['sources']['comparison']['sha256']
    audit = snapshot(audit_sha)
    snapshot(comparison_sha)
    require(audit['manifest_sha256'] == manifest_sha256 and
            audit['comparison_results_sha256'] == comparison_sha, 'Historical audit join mismatch')
    rows = list(overlay['rows'])
    extra = None
    if ref['sha256'] == APPROVED_OVERLAY96:
        wrapper = snapshot(APPROVED_OVERLAY96)
        require(wrapper['base_overlay']['sha256'] == APPROVED_OVERLAY, 'Historical base overlay mismatch')
        for dependency in wrapper['extra_sources'].values():
            snapshot(dependency['sha256'])
        extra = wrapper['extra_case']
        rows.append(extra)
    require(state.get('historical_evidence') == rows, 'Root historical evidence differs from snapshot')
    ids = {row['id'] for row in rows}
    require(len(ids) == (96 if extra else 95), 'Historical snapshot count mismatch')
    selected = set(state['selected_cases'])
    require(state.get('historical_skipped') == sorted(ids-selected), 'Historical skipped IDs mismatch')
    result = {}
    for row in rows:
        name = row['id']
        require(name in cases and cases[name]['sector'] == 'H1', 'Historical case missing from current index')
        original = cases[name]['row']
        require(original['tag'] == row['tag'] and int(original['profile']) == row['profile'],
                'Historical profile/tag differs from current index')
        result[name] = dict(row, overlay_sha256=APPROVED_OVERLAY,
                            audit_sha256=audit_sha, comparison_sha256=comparison_sha,
                            trust_basis='Reviewed 2005/2009 snapshots; inherited historical proof report, no new replay')
        if row is extra:
            result[name].update(overlay_sha256=APPROVED_OVERLAY96,
                                audit_sha256=wrapper['extra_sources']['audit']['sha256'],
                                comparison_sha256=wrapper['extra_sources']['comparison']['sha256'],
                                trust_basis='Reviewed 2014/2017 manifest-joined MONO snapshots; inherited historical proof report, no new replay')
    return result


def attach_history(row, historical):
    """Preserve fresh-attempt status and prohibit SAT/input conflicts from closing."""
    if historical is None:
        return row
    result = dict(row, historical_evidence=historical)
    hashes = {a['cnf_sha256'] for a in row['attempts'] if 'cnf_sha256' in a}
    if row['status'] in {'SAT_CANDIDATE', 'DISAGREEMENT'} or hashes - {historical['cnf_sha256']}:
        result['status'] = 'DISAGREEMENT'
    elif row['status'] == 'NOT_RUN':
        result['status'] = 'HISTORICAL_VERIFIED_UNSAT'
    # UNKNOWN/ERROR/INCOMPLETE remain explicit even with inherited evidence.
    return result
