import argparse
import json
import subprocess
import shutil
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

import cleanup_replay_work as target
import test_replay_transaction as fixtures
from replay_common import ReplayError, canonical_json, sha256_file


class CleanupTests(unittest.TestCase):
    def setUp(self):
        self.f = fixtures.ReplayTransactionTest()
        self.f.setUp()
        self.addCleanup(self.f.tearDown)
        manifest = json.loads(self.f.manifest.read_text())
        manifest.update(cleanup_accepted_work=True,
                        cleanup_sha256=sha256_file(Path(target.__file__)),
                        validator_sha256=sha256_file(target.VALIDATOR))
        self.f.manifest.write_bytes(canonical_json(manifest))
        self.args = argparse.Namespace(manifest=self.f.manifest, state_dir=self.f.state,
                                       object_store_root=self.f.store_root, s3_bucket=None, aws='aws')
        self.job = json.loads(self.f.job.read_text())
        self.dispatch = {'tag': self.f.tag, 'returncode': 0}

    def accepted(self):
        result = self.f.worker()
        self.assertEqual(result.returncode, 0, result.stderr)
        return self.f.state/'work'/self.f.tag

    def dispatch_queue(self):
        return subprocess.run([sys.executable, str(fixtures.DISPATCHER),
            '--manifest', str(self.f.manifest), '--queue', str(self.f.queue),
            '--state-dir', str(self.f.state), '--parallelism', '1', '--execute', 'YES',
            '--object-store-root', str(self.f.store_root)], capture_output=True, text=True)

    def test_dispatch_cleanup_and_accepted_resume_without_recompile(self):
        sibling = self.f.state/'work'/'fedcba9876543210'
        sibling.mkdir(parents=True); (sibling/'keep').write_text('unrelated')
        first = self.dispatch_queue()
        self.assertEqual(first.returncode, 0, first.stderr)
        receipt_sha = sha256_file(self.f.receipt_path())
        self.assertFalse((self.f.state/'work'/self.f.tag).exists())
        second = self.dispatch_queue()
        self.assertEqual(second.returncode, 0, second.stderr)
        row = json.loads((self.f.state/'dispatch'/'accepted'/f'{self.f.tag}.json').read_text())
        self.assertIn('ALREADY_ACCEPTED', row['stdout'])
        self.assertGreaterEqual(row['wall_ns'], row['worker_wall_ns'])
        self.assertEqual(sha256_file(self.f.receipt_path()), receipt_sha)
        self.assertEqual((sibling/'keep').read_text(), 'unrelated')
        journals = list((self.f.state/'cleanup').glob('*/cleanup.json'))
        self.assertEqual(len(journals), 2)
        for path in journals:
            record = json.loads(path.read_text())
            self.assertEqual(record['status'], 'DELETED')
            self.assertEqual(record['receipt_sha256'], receipt_sha)
            self.assertEqual(json.loads((path.parent/'validation.json').read_text())['returncode'], 0)

    def test_corrupt_live_artifact_retains_scratch(self):
        work = self.accepted()
        receipt = json.loads(self.f.receipt_path().read_text())
        artifact = self.f.store.objects / receipt['artifacts']['olean']['key']
        artifact.write_bytes(b'corrupt')
        with self.assertRaisesRegex(ReplayError, 'validation failed'):
            target.cleanup_accepted_work(self.args, self.job, self.dispatch)
        self.assertTrue(work.is_dir())
        validations = list((self.f.state/'cleanup').glob('*/validation.json'))
        self.assertEqual(len(validations), 1)
        self.assertNotEqual(json.loads(validations[0].read_text())['returncode'], 0)
        self.assertFalse(list((self.f.state/'cleanup').glob('*/cleanup.json')))

    def test_symlink_scratch_is_rejected_without_deleting_target(self):
        work = self.accepted()
        moved = self.f.root/'preserve'; work.rename(moved); work.symlink_to(moved, target_is_directory=True)
        with self.assertRaisesRegex(ReplayError, 'canonical'):
            target.cleanup_accepted_work(self.args, self.job, self.dispatch)
        self.assertTrue(moved.is_dir())
        self.assertTrue(work.is_symlink())

    def test_wrong_helper_pin_rejected_before_dispatch(self):
        manifest = json.loads(self.f.manifest.read_text()); manifest['cleanup_sha256'] = 'f'*64
        self.f.manifest.write_bytes(canonical_json(manifest))
        result = self.dispatch_queue()
        self.assertEqual(result.returncode, 2)
        self.assertIn('cleanup helper', result.stderr)
        self.assertFalse(self.f.receipt_path().exists())
        self.assertFalse((self.f.state/'dispatch'/'START.json').exists())

    def test_delete_interruption_preserves_pending_journal_and_resumes(self):
        work = self.accepted()
        real_delete = target.shutil.rmtree
        def fail_work(path, *args, **kwargs):
            if Path(path) == work:
                raise OSError('simulated cleanup interruption')
            return real_delete(path, *args, **kwargs)
        with patch.object(target.shutil, 'rmtree', side_effect=fail_work) as deletion:
            deletion.avoids_symlink_attacks = True
            with self.assertRaisesRegex(OSError, 'interruption'):
                target.cleanup_accepted_work(self.args, self.job, self.dispatch)
        pending = list((self.f.state/'cleanup').glob('*/cleanup.json'))
        self.assertEqual(json.loads(pending[0].read_text())['status'], 'VALIDATED_DELETE_PENDING')
        self.assertTrue(work.exists())
        target.cleanup_accepted_work(self.args, self.job, self.dispatch)
        self.assertFalse(work.exists())

    def test_nested_published_store_rejected_before_dispatch_and_preserved(self):
        work = self.accepted()
        nested = work/'published-store'
        shutil.copytree(self.f.store_root, nested)
        receipt = nested/'objects'/self.f.receipt_path().relative_to(self.f.store.objects)
        before = sha256_file(receipt)
        self.f.store_root = nested
        result = self.dispatch_queue()
        self.assertEqual(result.returncode, 2)
        self.assertIn('protected cleanup', result.stderr)
        self.assertEqual(sha256_file(receipt), before)
        self.assertTrue(work.is_dir())
        self.assertFalse((self.f.state/'dispatch'/'START.json').exists())
        self.args.object_store_root = nested
        with self.assertRaisesRegex(ReplayError, 'protected cleanup'):
            target.cleanup_accepted_work(self.args, self.job, self.dispatch)
        self.assertEqual(sha256_file(receipt), before)

    def test_symlink_store_and_protected_control_paths_rejected(self):
        work = self.accepted()
        manifest = json.loads(self.f.manifest.read_text())
        nested = work/'store'; nested.mkdir()
        alias = self.f.root/'store-alias'; alias.symlink_to(nested, target_is_directory=True)
        for store in (nested, alias):
            with self.subTest(store=store):
                args = argparse.Namespace(**vars(self.args)); args.object_store_root = store
                with self.assertRaisesRegex(ReplayError, 'protected cleanup'):
                    target.validate_cleanup_layout(args, manifest)
        for field in ('manifest', 'queue', 'lock'):
            args = argparse.Namespace(**vars(self.args)); current = dict(manifest)
            path = work/(field+'.control'); path.write_text('must retain')
            if field == 'lock': current['single_writer_lock_path'] = str(path)
            else: setattr(args, field, path)
            with self.subTest(field=field), self.assertRaisesRegex(ReplayError, 'protected cleanup'):
                target.validate_cleanup_layout(args, current)
            self.assertEqual(path.read_text(), 'must retain')

    def test_layout_is_rechecked_after_independent_validation(self):
        work = self.accepted()
        actual_run = target.subprocess.run
        def move_store_arg(*args, **kwargs):
            result = actual_run(*args, **kwargs)
            self.args.object_store_root = work/'late-store'
            return result
        with patch.object(target.subprocess, 'run', side_effect=move_store_arg):
            with self.assertRaisesRegex(ReplayError, 'protected cleanup'):
                target.cleanup_accepted_work(self.args, self.job, self.dispatch)
        self.assertTrue(work.exists())
        self.assertFalse(list((self.f.state/'cleanup').glob('*/cleanup.json')))

    def test_failure_stops_before_third_job_and_counts_skipped(self):
        jobs = [self.job]
        for i in (1, 2):
            tag = f'fedcba987654321{i}'
            jobs.append(dict(self.job, tag=tag, local_index=i,
                certificate_key=f'sat49/campaign-20260825/h1/{tag}.compact.lrat.gz'))
        self.f.queue.write_bytes(b''.join(canonical_json(job) for job in jobs))
        manifest = json.loads(self.f.manifest.read_text())
        manifest.update(queue_sha256=sha256_file(self.f.queue), expected_jobs=3)
        self.f.manifest.write_bytes(canonical_json(manifest))
        result = self.dispatch_queue()
        self.assertEqual(result.returncode, 2, result.stdout+result.stderr)
        end = json.loads((self.f.state/'dispatch'/'END.json').read_text())
        self.assertEqual((end['accepted'], end['failed'], end['scheduled']), (1, 1, 2))
        self.assertEqual(end['skipped_tags'], [jobs[2]['tag']])
        self.assertFalse((self.f.state/'work'/self.f.tag).exists())
        self.assertTrue((self.f.state/'work'/jobs[1]['tag']).exists())
        self.assertFalse((self.f.state/'jobs'/f"{jobs[2]['tag']}.json").exists())


if __name__ == '__main__':
    unittest.main()
