"""Exercise pinned metadata and controller functions with no AWS/solver execution."""
import argparse
import ast
import base64
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace

COMMIT = '797579e113ab59e1bcbcb93eb0b84540b628ded0'
R = 'research/problems/erdos-85-wip-01'
PKG = R + '/h7_hsb_campaign_20261008'
IDS = ['cube_F6_t14-cover', 'cube_F7_t10-cover', 'cube_F6_t14-b0000', 'cube_F6_t18-b0000',
       'cube_F7_t10-b0000', 'cube_F7_t13-b0000', 'cube_F8_t0-b0000', 'cube_F9_t0-b0000']


def function(source, name):
    return next(n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef) and n.name == name)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repository', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    a.output.mkdir(exist_ok=False)
    sources = {}
    for name in ['cert_worker.py', 'cert_controller.py', 'cert_bootstrap.sh', 'h7_common.py',
                 'cert_item.py', 'cert_batch.py', 'collect_receipts.py', 'test_campaign.py', 'receipts/inputs.json']:
        path = PKG + '/' + name
        sources[path] = subprocess.check_output(['git', '-C', str(a.repository), 'show', COMMIT + ':' + path])
    path = R + '/h1_cert_full_20261001/cert_row.py'
    sources[path] = subprocess.check_output(['git', '-C', str(a.repository), 'show', COMMIT + ':' + path])
    proposed = Path(__file__).resolve().parent.parent / 'h7_canary_limit_review_20261008/cert_worker.proposed.py'
    worker = sources[PKG + '/cert_worker.py'].decode()
    assert ast.dump(function(worker, 'slot_loop')) == ast.dump(function(proposed.read_text(), 'slot_loop'))
    with tempfile.TemporaryDirectory(prefix='e85-integrated-canary-metadata-') as tmp:
        for name, data in sources.items():
            target = Path(tmp) / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        package = Path(tmp) / PKG
        run = subprocess.run([sys.executable, '-B', str(package / 'test_campaign.py')], capture_output=True)
        (a.output / 'in-tree-tests.log').write_bytes(run.stdout + run.stderr)
        assert run.returncode == 0 and b'Ran 16 tests' in run.stderr and b'\nOK\n' in run.stderr
        spec = importlib.util.spec_from_file_location('reviewed_common', package / 'h7_common.py')
        hc = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(hc)
        meta = json.loads(sources[PKG + '/receipts/inputs.json'])
        rows = hc.batches(meta)
        selection = hc.canary_rows(meta)
        assert [r['id'] for r in selection] == IDS and len(set(IDS)) == 8
        assert all(r['kind'] == 'cover' for r in rows[:28])
        assert sum(r['kind'] == 'cover' for r in selection) == 2
        leaves = [r for r in selection if r['kind'] == 'leaves']
        assert len(leaves) == 6 and all(r['start'] == 0 and r['end'] == 64 for r in leaves)
        assert len({r['cube'] for r in leaves}) == 6
        assert sum(hc.row_items(r) for r in selection) == 386
        controller = sources[PKG + '/cert_controller.py'].decode()
        watch = function(controller, 'one_pass')
        watcher_cases = []
        for label, manifest, complete, expect_stop in [
            ('full_manifest_canary_only', rows, selection, False),
            ('full_manifest_all_certified', rows, rows, True),
            ('restricted_manifest_all_certified', selection, selection, True)]:
            stops = []
            ledgers = [dict(r, status='CERTIFIED', items=hc.row_items(r)) for r in complete]
            vc = SimpleNamespace(PASS={'size': len(manifest)}, HARD_STOP_USD=160,
                                 stop=lambda arg: stops.append(arg))
            namespace = {'vc': vc, '_reviewed_one_pass': lambda state, act: {},
                         'MANIFEST': manifest, 'ledgers': lambda: ledgers}
            exec(compile(ast.Module(body=[watch], type_ignores=[]), '<pinned one_pass>', 'exec'), namespace)
            report = namespace['one_pass']({}, True)
            assert bool(stops) == expect_stop
            assert report['certified_batches'] == len(complete)
            watcher_cases.append({'case': label, 'stop_called': bool(stops), 'report': report})
        args = SimpleNamespace(manifest='', only=','.join(IDS), lifetime=129600, heap_mb=2000,
                               cap=3600, max_batches=0, partial_seconds=120, commit=COMMIT)
        namespace = {'SPARSE': [], 'BRANCH': 'erdos85/h7t0-formal-20261007', 'base64': base64,
                     'Path': Path, 'inputs_sha': lambda: 'a' * 64, 'manifest_sha': lambda _: 'b' * 64,
                     'vc': SimpleNamespace(REGION='us-east-1', BUCKET='fixture', PREFIX='fixture')}
        exec(compile(ast.Module(body=[function(controller, 'user_data')], type_ignores=[]), '<pinned user_data>', 'exec'), namespace)
        generated = base64.b64decode(namespace['user_data'](args)).decode()
        assert "E85_ONLY='" + ','.join(IDS) + "'" in generated
        assert "E85_PARTIAL_SECONDS='120'" in generated and "E85_MANIFEST_KEY=''" in generated
    result = {'status': 'METADATA_REVIEW_PASS', 'commit': COMMIT,
              'slot_loop_equals_reviewed_proposal_ast': True, 'in_tree_unit_tests': 16,
              'selection': selection, 'canary_items': 386, 'main_manifest_rows': len(rows),
              'watcher_cases': watcher_cases, 'user_data_selector_and_interval_pass': True,
              'sources_sha256': {n: hashlib.sha256(d).hexdigest() for n, d in sources.items()},
              'scope': 'Pinned source with mocked store/batches/watch backend; no solver, AWS operation, or Lean run.'}
    (a.output / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'in_tree_unit_tests', 'canary_items', 'main_manifest_rows']}))


if __name__ == '__main__':
    main()
