"""Synthetic run receipts around genuine pinned input snapshots; no solving."""
import json
import tempfile
from pathlib import Path
import unittest

import summarize_phase_b_verdicts as reducer
from test_reviewed_historical_snapshot import ROOT


class IntegrationTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.run=Path(self.tmp.name)
        snapshots=self.run/'snapshots'
        snapshots.mkdir()
        config_path=ROOT/'phase_b_historical_overlay/config.draft.json'
        config_raw=config_path.read_bytes()
        config=json.loads(config_raw)
        self.index=ROOT/'phase_b_survivors_20260910.json'
        self.index_sha=config['index']['sha256']
        index=json.loads(self.index.read_bytes())
        paths=[config_path,self.index]
        paths += [ROOT/'sat49'/name for name in config['tool_sha256']]
        paths += [self.index.parent/ref['path'] for ref in index['sources'].values()]
        overlay_path=config_path.parent/config['historical_overlay']['path']
        overlay=json.loads(overlay_path.read_bytes())
        paths += [overlay_path]+[overlay_path.parent/ref['path'] for ref in overlay['sources'].values()]
        for i,path in enumerate(paths):
            (snapshots/f'{i:02d}-{path.name}').write_bytes(path.read_bytes())
        self.state=dict(schema='erdos85-dispatch-results-v1',index_sha256=self.index_sha,
                        config_sha256=reducer.digest(config_raw),config_commit='2bf321a03da920a737bdcae6815dcdcf9f00d4fc',
                        inventory_cases=1416,proof_logging=False,selected_cases=[],results=[],status='complete',
                        historical_evidence=overlay['rows'],historical_skipped=sorted(r['id'] for r in overlay['rows']),
                        not_started=[])

    def summarize(self):
        (self.run/'results.json').write_text(json.dumps(self.state))
        return reducer.summarize(self.index,self.index_sha,[self.run])

    def use96(self):
        config_path=ROOT/'phase_b_historical_overlay_96/config.draft.json'
        raw=config_path.read_bytes();config=json.loads(raw)
        wrapper_path=config_path.parent/config['historical_overlay']['path']
        wrapper=json.loads(wrapper_path.read_text())
        paths=[config_path,wrapper_path]+[wrapper_path.parent/ref['path'] for ref in wrapper['extra_sources'].values()]
        for i,path in enumerate(paths):
            (self.run/'snapshots'/f'extra-{i}-{path.name}').write_bytes(path.read_bytes())
        self.state['config_sha256']=reducer.digest(raw)
        self.state['historical_evidence'].append(wrapper['extra_case'])
        self.state['historical_skipped']=sorted(r['id'] for r in self.state['historical_evidence'])
        return wrapper['extra_case']['id']

    def test_mixed95_96_runs_reconcile_without_duplicate_history(self):
        self.summarize()
        other=IntegrationTests()
        other.setUp()
        try:
            other.use96();other.summarize()
            result=reducer.summarize(self.index,self.index_sha,[self.run,other.run])
            self.assertEqual(result['historical_evidence_cases'],96)
            self.assertEqual(result['counts'],{'NOT_RUN':1320,'HISTORICAL_VERIFIED_UNSAT':96})
            self.assertFalse(result['all_targets_crosschecked_unsat'])
        finally:other.doCleanups()

    def test_extra96_partial_sat_is_not_hidden_by_history(self):
        name=self.use96()
        self.state['historical_skipped'].remove(name)
        self.state.update(selected_cases=[name],status='running')
        self.state.pop('not_started')
        log=self.run/name/'solve'/name/'cadical.log'
        log.parent.mkdir(parents=True)
        log.write_text('s SATISFIABLE\n')
        result=self.summarize()
        row=next(r for r in result['rows'] if r['id']==name)
        self.assertEqual(row['status'],'DISAGREEMENT')
        self.assertEqual(row['historical_evidence']['evidence_format'],'manifest_joined_mono')
        self.assertFalse(result['all_targets_crosschecked_unsat'])

    def test_historical_only_does_not_claim_fresh_closure(self):
        result=self.summarize()
        self.assertEqual(result['counts'],{'NOT_RUN':1321,'HISTORICAL_VERIFIED_UNSAT':95})
        self.assertEqual(result['historical_evidence_cases'],95)
        self.assertFalse(result['all_targets_crosschecked_unsat'])
        self.assertFalse(result['has_disagreement'])

    def test_reselected_historical_partial_sat_stops_closure(self):
        name=self.state['historical_skipped'].pop()
        self.state.update(selected_cases=[name],status='running')
        self.state.pop('not_started')
        log=self.run/name/'solve'/name/'kissat.log'
        log.parent.mkdir(parents=True)
        log.write_text('s SATISFIABLE\n')
        result=self.summarize()
        row=next(r for r in result['rows'] if r['id']==name)
        self.assertEqual(row['status'],'DISAGREEMENT')
        self.assertIn('historical_evidence',row)
        self.assertEqual(len(row['attempts']),1)
        self.assertTrue(result['has_disagreement'])

    def test_reselected_historical_incomplete_stays_explicit(self):
        name=self.state['historical_skipped'].pop()
        self.state.update(selected_cases=[name],status='running')
        self.state.pop('not_started')
        result=self.summarize()
        row=next(r for r in result['rows'] if r['id']==name)
        self.assertEqual(row['status'],'INCOMPLETE')
        self.assertIn('historical_evidence',row)


if __name__=='__main__':
    unittest.main()
