"""Read-only tests against the already banked historical snapshot fixtures."""
import copy
import hashlib
import json
from pathlib import Path
import unittest

import reviewed_historical_snapshot as history

ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')


class HistoricalTests(unittest.TestCase):
    def setUp(self):
        path=ROOT/'phase_b_historical_overlay/historical-95.json'
        raw=path.read_bytes()
        self.overlay=json.loads(raw)
        self.snapshots={hashlib.sha256(raw).hexdigest():raw}
        for ref in self.overlay['sources'].values():
            data=(path.parent/ref['path']).read_bytes()
            self.snapshots[hashlib.sha256(data).hexdigest()]=data
        raw=(ROOT/'phase_b_h1_h3/h1-frozen-candidates.json').read_bytes()
        self.manifest_sha=hashlib.sha256(raw).hexdigest()
        self.cases={row['id']:dict(sector='H1',row=row) for row in json.loads(raw)['rows']}
        self.config={'historical_overlay':{'sha256':history.APPROVED_OVERLAY}}
        self.state=dict(historical_evidence=copy.deepcopy(self.overlay['rows']),selected_cases=[],
                        historical_skipped=sorted(row['id'] for row in self.overlay['rows']))

    def load(self):
        return history.load_reviewed_history(self.config,self.snapshots,self.state,self.cases,self.manifest_sha)

    def test_exact_reviewed_set_and_explicit_resolve(self):
        records=self.load()
        self.assertEqual(len(records),95)
        name=next(iter(records))
        self.state['selected_cases']=[name]
        self.state['historical_skipped'].remove(name)
        self.assertEqual(self.load(),records)

    def test_unreviewed_overlay_refused(self):
        self.config['historical_overlay']['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'not the reviewed'):
            self.load()

    def use96(self):
        path=ROOT/'phase_b_historical_overlay_96/historical-96.json'
        raw=path.read_bytes();wrapper=json.loads(raw)
        self.snapshots[hashlib.sha256(raw).hexdigest()]=raw
        for ref in wrapper['extra_sources'].values():
            data=(path.parent/ref['path']).read_bytes()
            self.snapshots[hashlib.sha256(data).hexdigest()]=data
        self.config['historical_overlay']['sha256']=history.APPROVED_OVERLAY96
        self.state['historical_evidence'].append(wrapper['extra_case'])
        self.state['historical_skipped']=sorted(r['id'] for r in self.state['historical_evidence'])
        return wrapper

    def test96_retains_old_provenance_and_separates_extra_format(self):
        old=self.load();wrapper=self.use96();records=self.load()
        self.assertEqual(len(records),96)
        self.assertEqual({name:records[name] for name in old},old)
        extra=records[wrapper['extra_case']['id']]
        self.assertEqual(extra['evidence_format'],'manifest_joined_mono')
        self.assertEqual(extra['audit_sha256'],wrapper['extra_sources']['audit']['sha256'])
        self.assertEqual(extra['overlay_sha256'],history.APPROVED_OVERLAY96)

    def test96_extra_dependency_and_root_row_are_required(self):
        wrapper=self.use96();sha=wrapper['extra_sources']['comparison']['sha256']
        raw=self.snapshots.pop(sha)
        with self.assertRaisesRegex(ValueError,'Missing historical'):
            self.load()
        self.snapshots[sha]=raw
        self.state['historical_evidence'].pop()
        with self.assertRaisesRegex(ValueError,'differs from snapshot'):
            self.load()

    def test_changed_or_missing_snapshots_refused(self):
        sha=self.overlay['sources']['audit']['sha256']
        raw=self.snapshots.pop(sha)
        with self.assertRaisesRegex(ValueError,'Missing historical'):
            self.load()
        self.snapshots[sha]=raw+b' '
        with self.assertRaisesRegex(ValueError,'bytes mismatch'):
            self.load()

    def test_root_cannot_add_or_omit_historical_rows(self):
        self.state['historical_evidence'].pop()
        with self.assertRaisesRegex(ValueError,'differs from snapshot'):
            self.load()

    def test_skipped_set_must_match_selection(self):
        self.state['historical_skipped'].pop()
        with self.assertRaisesRegex(ValueError,'skipped IDs'):
            self.load()

    def test_fresh_results_remain_distinct_and_conflicts_stop_closure(self):
        record=next(iter(self.load().values()))
        for state in ('NOT_RUN','UNKNOWN','ERROR','INCOMPLETE','UNSAT_PRIMARY','UNSAT_CROSSCHECKED','SAT_CANDIDATE'):
            with self.subTest(state=state):
                row=dict(status=state,attempts=[])
                out=history.attach_history(row,record)
                expected={'NOT_RUN':'HISTORICAL_VERIFIED_UNSAT','SAT_CANDIDATE':'DISAGREEMENT'}.get(state,state)
                self.assertEqual(out['status'],expected)
                self.assertEqual(row['status'],state)
        row=dict(status='UNSAT_CROSSCHECKED',attempts=[{'cnf_sha256':'0'*64}])
        self.assertEqual(history.attach_history(row,record)['status'],'DISAGREEMENT')


if __name__=='__main__':
    unittest.main()
