"""Tiny metadata and mocked control checks; no solver, Lean, or AWS execution."""
import ast
import copy
import importlib.util
import json
import subprocess
import unittest
from pathlib import Path

import audit_receipts as audit

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT/'snapshot1/source'
INPUTS = ROOT/'inputs.json'


def main():
    # Reuse only the peer's mocked reservation tests against our immutable worker snapshot.
    tree = ast.parse((SOURCE/'test_campaign.py').read_text())
    picked = [n for n in tree.body if getattr(n, 'name', '') in ('exercise_slot_loop', 'Reservation')]
    env = {'HERE': SOURCE, 'Path': Path, 'unittest': unittest}
    exec(compile(ast.Module(body=picked, type_ignores=[]), 'pinned-reservation-tests', 'exec'), env)
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(env['Reservation'])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    assert result.wasSuccessful()

    # All these operations are metadata only: no formula bytes or SAT/Lean imports.
    spec = importlib.util.spec_from_file_location('reviewed_h7_common', SOURCE/'h7_common.py')
    hc = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(hc)
    meta = json.loads(INPUTS.read_bytes())
    rows = hc.batches(meta)
    assert len(rows) == 12605 and len({r['id'] for r in rows}) == len(rows)
    assert hc.sha_bytes(hc.manifest_bytes(meta)) == audit.MANIFEST
    covers = [r['cube'] for r in rows if r['kind'] == 'cover']
    assert len(covers) == len(set(covers)) == 28 and set(covers) == set(meta['cubes'])
    total = 0
    for cube in covers:
        spans = sorted((r['start'], r['end']) for r in rows if r['cube'] == cube and r['kind'] == 'leaves')
        cursor = 0
        for start, end in spans:
            assert start == cursor and end > start
            cursor = end
        assert cursor == meta['cubes'][cube]['leaves']
        total += cursor
    assert total == 377776
    selected = hc.canary_rows(meta)
    assert {r['id'] for r in selected} == set(audit.ROWS)
    for r in selected:
        assert audit.ROWS[r['id']] == (r['cube'], [None] if r['kind'] == 'cover' else list(range(r['start'], r['end'])))

    # Check that dangerous receipt mutations are rejected by the independent item validator.
    path = next((ROOT/'snapshot1/canary/results').glob('cube_F6_t16-b0000.*'))
    r = json.loads(subprocess.check_output(['zstd', '-dc', str(path)]).splitlines()[0])
    hosts = {r['host']: 'original-node'}
    audit.item_check(r, r['batch'], r['cube'], r['leaf'], hosts, meta)
    changes = [(('status',), 'SOLVER_TIMEOUT'), (('binaries', 'cake_lpr'), '0'*64),
               (('checker', 'verified_line'), False), (('checker', 'returncode'), 1),
               (('checker', 'heap_mb'), 2000), (('solver', 'returncode'), 0),
               (('solver', 'unsat_line'), False), (('proof', 'checker_closed_early'), True),
               (('proof', 'sha256'), ''), (('cnf_sha256',), '0'*64), (('host',), 'unknown'),
               (('leaf',), 0), (('units',), [1])]
    for keys, value in changes:
        bad = copy.deepcopy(r)
        target = bad
        for key in keys[:-1]:
            target = target[key]
        target[keys[-1]] = value
        try:
            audit.item_check(bad, r['batch'], r['cube'], r['leaf'], hosts, meta)
        except AssertionError:
            pass
        else:
            raise AssertionError(('accepted mutated receipt', keys))
    print(json.dumps({'status': 'METADATA_AND_MOCKED_CONTROL_CHECKS_PASS',
                      'reservation_tests': result.testsRun, 'rejected_receipt_mutations': len(changes),
                      'manifest_rows': len(rows), 'leaf_coverage': total, 'covers': 28,
                      'manifest_sha256': audit.MANIFEST, 'cloud_calls': 0}))


if __name__ == '__main__':
    main()
