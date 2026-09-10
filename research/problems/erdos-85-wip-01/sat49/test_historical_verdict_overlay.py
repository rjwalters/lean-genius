import copy
import contextlib
import io
import sys
from unittest.mock import patch
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import historical_verdict_overlay as h


class HistoricalTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.path=Path(self.temp.name)/'overlay.json'
        base=Path(__file__).resolve().parent.parent
        original=base/'phase_b_historical_overlay/historical-95.json'
        self.data=json.loads(original.read_bytes())
        for ref in self.data['sources'].values():ref['path']=str((original.parent/ref['path']).resolve())
        self.frozen=(base/'phase_b_h1_h3/h1-frozen-candidates.json').read_bytes()

    def load(self):
        raw=json.dumps(self.data).encode();self.path.write_bytes(raw)
        return h.load_overlay(self.path,hashlib.sha256(raw).hexdigest(),self.frozen)

    def test_real_exact_95_join(self):
        rows,captured=self.load()
        self.assertEqual(len(rows),95);self.assertEqual(len(captured),3)
        self.assertTrue(all(r['proof_replayed'] is False for r in rows))

    def test_dispatch_selection_and_forced_crosscheck(self):
        import dispatch_verdict_only as d
        base=Path(__file__).resolve().parent.parent
        config=json.loads((base/'phase_b_historical_overlay/config.draft.json').read_text())
        config['index']['path']=str(base/'phase_b_survivors_20260910.json')
        config['historical_overlay']['path']=str(base/'phase_b_historical_overlay/historical-95.json')
        path=Path(self.temp.name)/'config.json'
        def run(extra=()):
            path.write_text(json.dumps(config))
            with patch.object(sys,'argv',['dispatch','--config',str(path),*extra]),contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(d.main(),0)
            return json.loads(output.getvalue())
        result=run();self.assertEqual(result['selected_cases'],1321)
        self.assertEqual(len(result['historical_skipped']),95)
        first=self.data['rows'][0]['id']
        config['crosscheck_ids']=[first]
        result=run();self.assertEqual(result['selected_cases'],1322)
        self.assertNotIn(first,result['historical_skipped'])
        result=run(['--case-id',first]);self.assertEqual(result['selected_cases'],1)
        plan=d.load_plan(path)
        self.assertEqual(len(plan['captured']),14)
        self.assertTrue(next(c for c in plan['cases'] if c['id']==first)['policy']['crosscheck'])

    def test_missing_row_rejected(self):
        self.data['rows'].pop();self.data['count']=94
        with self.assertRaisesRegex(ValueError,'exact 95'):self.load()

    def test_duplicate_row_rejected(self):
        self.data['rows'][1]=copy.deepcopy(self.data['rows'][0])
        with self.assertRaisesRegex(ValueError,'Duplicate historical'):self.load()

    def test_unpaired_case_rejected(self):
        self.data['rows'][0]['tag']='2c22b4969bc68443'
        self.data['rows'][0]['id']='h1_2c22b4969bc68443'
        with self.assertRaisesRegex(ValueError,'eligible set'):self.load()

    def test_changed_cnf_identity_rejected(self):
        self.data['rows'][0]['cnf_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'CNF join'):self.load()

    def test_changed_dependency_rejected(self):
        self.data['sources']['audit']['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'audit snapshot'):self.load()

    def test_unknown_cannot_be_historical_unsat(self):
        e=self.data['rows'][0]['evidence'][0];e['verdict']=e['verdict'].replace(' UNSAT ',' UNKNOWN ')
        e['verdict_sha256']=hashlib.sha256(e['verdict'].encode()).hexdigest()
        with self.assertRaisesRegex(ValueError,'status mismatch'):self.load()

    def test_cube_mode_rejected(self):
        e=self.data['rows'][0]['evidence'][0];e['verdict']=e['verdict'].replace('mode:MONO','mode:CUBE25')
        with self.assertRaisesRegex(ValueError,'status mismatch'):self.load()

    def test_verdict_table_change_rejected(self):
        e=self.data['rows'][0]['evidence'][0];e['verdict']=e['verdict'].split('table:')[0]+'table:[]\n'
        e['verdict_sha256']=hashlib.sha256(e['verdict'].encode()).hexdigest()
        with self.assertRaisesRegex(ValueError,'table mismatch'):self.load()

    def test_replay_claim_rejected(self):
        self.data['rows'][0]['proof_replayed']=True
        with self.assertRaisesRegex(ValueError,'scope changed'):self.load()


if __name__=='__main__':unittest.main()
