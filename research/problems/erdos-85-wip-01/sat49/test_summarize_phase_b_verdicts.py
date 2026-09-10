import json
from pathlib import Path
import tempfile
import unittest

import summarize_phase_b_verdicts as r


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.index_path = self.root/'index.json'
        sources, cases = {}, []
        for sector in sorted(r.SECTORS):
            row = dict(id=sector.lower(), cnf_sha256='a'*64, variables=3,
                       clauses=2, bytes=24, generator_commit='b'*40)
            path = self.root/f'{sector}.json'
            self.write(path, {'rows': [row]})
            sources[sector] = dict(path=path.name, sha256=r.digest(path.read_bytes()),
                                   array='rows', count=1)
            cases.append(dict(id=row['id'], sector=sector, source_index=0, cnf_sha256=row['cnf_sha256']))
        self.write(self.index_path, dict(schema='erdos85-phase-b-combined-inventory-v1',
                    sources=sources, counts={s:1 for s in r.SECTORS}, total=4, cases=cases))
        self.index_sha = r.digest(self.index_path.read_bytes())
        self.sources = sources

    def write(self, path, data):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data)+'\n')

    def run_fixture(self, name, primary='UNSAT', secondary='UNSAT', missing=False):
        run = self.root/name
        snapshots = run/'snapshots'
        snapshots.mkdir(parents=True)
        for path in self.root.glob('*.json'):
            (snapshots/path.name).write_bytes(path.read_bytes())
        tools = {}
        for tool in r.TOOLS:
            raw = ('synthetic test tool '+tool).encode()
            (snapshots/tool).write_bytes(raw)
            tools[tool] = r.digest(raw)
        config = dict(schema='erdos85-dispatch-v1', index={'sha256':self.index_sha}, tool_sha256=tools,
                      policies={s:dict(crosscheck=True, primary_cap_seconds=5, crosscheck_cap_seconds=5)
                                for s in r.SECTORS}, crosscheck_ids=[])
        self.write(snapshots/'config.json', config)
        state = dict(schema='erdos85-dispatch-results-v1', index_sha256=self.index_sha,
                     config_sha256=r.digest((snapshots/'config.json').read_bytes()), config_commit='b'*40,
                     inventory_cases=4, proof_logging=False, selected_cases=['h3'], status='running',
                     solvers={s:dict(path='/fake/'+s, sha256=r.digest(s.encode())) for s in ('kissat','cadical')},
                     results=[])
        if not missing:
            prepared = dict(id='h3', sector='H3', manifest_sha256=self.sources['H3']['sha256'],
                            cnf_sha256='a'*64, cnf_path='/fake/input.cnf', status='validated_existing',
                            generated=False, variables=3, clauses=2, bytes=24, generator_commit='b'*40)
            def solver(kind, verdict):
                text, rc, stop = {'UNSAT':('s UNSATISFIABLE\n',20,None),
                                 'SAT_CANDIDATE':('s SATISFIABLE\n',10,None),
                                 'UNKNOWN':('s UNSATISFIABLE\n',20,'wall cap')}[verdict]
                raw=text.encode()
                path=run/'h3/solve/h3'/f'{kind}.log'
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
                options=['--time=5'] if kind=='kissat' else ['-t','5']
                return dict(command=['/fake/'+kind,*options,prepared['cnf_path']],
                            solver_sha256=state['solvers'][kind]['sha256'], returncode=rc, stop_reason=stop,
                            verdict=verdict, log_sha256=r.digest(raw), log_bytes=len(raw), proof_requested=False)
            status = {'UNSAT':'UNSAT_CROSSCHECKED','UNKNOWN':'UNKNOWN','SAT_CANDIDATE':'DISAGREEMENT'}[secondary] if primary=='UNSAT' else primary
            solved=dict(id='h3',sector='H3',cnf_sha256='a'*64,generator_commit='b'*40,
                        status=status,primary=solver('kissat',primary))
            if primary=='UNSAT':
                solved['crosscheck']=solver('cadical',secondary)
            record=dict(id='h3',sector='H3',index_sha256=self.index_sha,status=status,
                        cnf_sha256='a'*64,preparation=prepared,solve=solved)
            self.write(run/'h3/preparation.json',prepared)
            self.write(run/'h3/solve/h3/result.json',solved)
            self.write(run/'h3/result.json',record)
            state.update(results=[record],status='complete',not_started=[])
        self.write(run/'results.json',state)
        return run

    def summary(self, *runs):
        return r.summarize(self.index_path,self.index_sha,runs)

    def test_no_run_is_not_unsat(self):
        result=self.summary()
        self.assertEqual(result['counts'],{'NOT_RUN':4})
        self.assertFalse(result['all_targets_crosschecked_unsat'])

    def test_pilot_does_not_close_inventory(self):
        result=self.summary(self.run_fixture('pilot'))
        self.assertEqual(result['counts'],{'NOT_RUN':3,'UNSAT_CROSSCHECKED':1})
        self.assertFalse(result['all_targets_crosschecked_unsat'])

    def test_secondary_cap_after_unsat_is_unknown(self):
        self.assertEqual(self.summary(self.run_fixture('cap',secondary='UNKNOWN'))['counts'],
                         {'NOT_RUN':3,'UNKNOWN':1})

    def test_conflicting_attempts_retained(self):
        result=self.summary(self.run_fixture('unsat'),self.run_fixture('sat',primary='SAT_CANDIDATE'))
        row=next(x for x in result['rows'] if x['id']=='h3')
        self.assertEqual(row['status'],'DISAGREEMENT')
        self.assertEqual(len(row['attempts']),2)
        self.assertTrue(result['has_disagreement'])

    def test_incomplete_and_not_started_differ(self):
        run=self.run_fixture('missing',missing=True)
        self.assertEqual(self.summary(run)['counts'],{'NOT_RUN':3,'INCOMPLETE':1})
        state=json.loads((run/'results.json').read_text())
        state.update(status='stopped',not_started=['h3'])
        self.write(run/'results.json',state)
        self.assertEqual(self.summary(run)['counts'],{'NOT_RUN':4})

    def test_tampered_log_refused(self):
        run=self.run_fixture('tamper')
        (run/'h3/solve/h3/kissat.log').write_text('s SATISFIABLE\n')
        with self.assertRaisesRegex(ValueError,'log identity'):
            self.summary(run)

    def test_case_root_mismatch_refused(self):
        run=self.run_fixture('tamper')
        path=run/'h3/result.json'
        record=json.loads(path.read_text())
        record['cnf_sha256']='c'*64
        self.write(path,record)
        with self.assertRaisesRegex(ValueError,'Invocation/case'):
            self.summary(run)

    def test_missing_snapshot_refused(self):
        run=self.run_fixture('tamper')
        (run/'snapshots/H1.json').unlink()
        with self.assertRaisesRegex(ValueError,'transitive'):
            self.summary(run)

    def test_input_identity_conflict_blocks_closure(self):
        attempts=[dict(status='UNSAT_CROSSCHECKED',cnf_sha256='a'*64),
                  dict(status='UNSAT_CROSSCHECKED',cnf_sha256='b'*64)]
        self.assertEqual(r.combine(attempts,False),'DISAGREEMENT')

    def test_error_after_sat_cannot_be_overridden_by_unsat(self):
        run=self.run_fixture('sat',primary='SAT_CANDIDATE')
        state=json.loads((run/'results.json').read_text())
        state['results'][0]['status']='ERROR'
        state['results'][0]['error']='post-solve source changed'
        self.write(run/'results.json',state)
        self.write(run/'h3/result.json',state['results'][0])
        result=self.summary(run,self.run_fixture('unsat'))
        self.assertTrue(result['has_disagreement'])
        self.assertFalse(result['all_targets_crosschecked_unsat'])

    def test_unpublished_sat_at_each_worker_boundary(self):
        good=self.run_fixture('earlier-unsat')
        for boundary in ('wrapper', 'solver', 'log'):
            with self.subTest(boundary=boundary):
                run=self.run_fixture('later-'+boundary,primary='SAT_CANDIDATE')
                state=json.loads((run/'results.json').read_text())
                state.update(results=[],status='running')
                state.pop('not_started')
                self.write(run/'results.json',state)
                if boundary in ('solver','log'):
                    (run/'h3/result.json').unlink()
                if boundary=='log':
                    (run/'h3/solve/h3/result.json').unlink()
                result=self.summary(good,run)
                row=next(x for x in result['rows'] if x['id']=='h3')
                self.assertEqual(row['status'],'DISAGREEMENT')
                self.assertEqual(len(row['attempts']),2)
                self.assertTrue(row['attempts'][1]['sat_alarm'])
                self.assertTrue(row['attempts'][1]['artifacts'])

    def test_unpublished_unknown_blocks_previous_unsat_closure(self):
        good=self.run_fixture('earlier-unsat')
        run=self.run_fixture('later-unknown',primary='UNKNOWN')
        state=json.loads((run/'results.json').read_text())
        state.update(results=[],status='running')
        state.pop('not_started')
        self.write(run/'results.json',state)
        result=self.summary(good,run)
        row=next(x for x in result['rows'] if x['id']=='h3')
        self.assertEqual(row['status'],'INCOMPLETE')
        self.assertEqual(len(row['attempts']),2)

    def test_published_error_without_solve_field_retains_sat_log_alarm(self):
        run=self.run_fixture('error',primary='SAT_CANDIDATE')
        state=json.loads((run/'results.json').read_text())
        record=dict(id='h3',sector='H3',index_sha256=self.index_sha,status='ERROR',error='worker crash')
        state['results']=[record]
        self.write(run/'results.json',state)
        self.write(run/'h3/result.json',record)
        (run/'h3/solve/h3/result.json').unlink()
        result=self.summary(self.run_fixture('earlier-unsat'),run)
        self.assertTrue(result['has_disagreement'])

    def test_published_capped_sat_is_alarm_for_primary_and_secondary(self):
        for kind in ('primary','crosscheck'):
            with self.subTest(kind=kind):
                run=self.run_fixture('capped-'+kind,primary='UNKNOWN' if kind=='primary' else 'UNSAT',secondary='UNKNOWN')
                log=run/'h3/solve/h3'/('kissat.log' if kind=='primary' else 'cadical.log')
                raw=b's SATISFIABLE\n'
                log.write_bytes(raw)
                state=json.loads((run/'results.json').read_text())
                record=state['results'][0]
                receipt=record['solve'][kind]
                receipt.update(log_sha256=r.digest(raw),log_bytes=len(raw),returncode=10)
                self.write(run/'results.json',state)
                self.write(run/'h3/result.json',record)
                self.write(run/'h3/solve/h3/result.json',record['solve'])
                result=self.summary(self.run_fixture('good-'+kind),run)
                row=next(x for x in result['rows'] if x['id']=='h3')
                self.assertEqual(row['status'],'DISAGREEMENT')
                self.assertEqual(row['attempts'][1]['status'],'UNKNOWN')
                self.assertTrue(row['attempts'][1]['sat_alarm'])

    def test_error_then_success_keeps_attempt(self):
        run=self.run_fixture('failed',missing=True)
        state=json.loads((run/'results.json').read_text())
        record=dict(id='h3',sector='H3',index_sha256=self.index_sha,status='ERROR',error='generation failed')
        self.write(run/'h3/result.json',record)
        state.update(results=[record],status='stopped',not_started=[])
        self.write(run/'results.json',state)
        result=self.summary(run,self.run_fixture('retry'))
        row=next(x for x in result['rows'] if x['id']=='h3')
        self.assertEqual(row['status'],'UNSAT_CROSSCHECKED')
        self.assertEqual([a['status'] for a in row['attempts']],['ERROR','UNSAT_CROSSCHECKED'])

    def test_h1_historical_and_new_preparation(self):
        for historical in (None,'a'*64):
            with self.subTest(historical=historical):
                row=dict(tag='fixture',profile=0,table_values=[0]*24,historical_cnf_sha256=historical)
                case=dict(id='h1',sector='H1',row=row)
                config=dict(h1_generator_commit='b'*40,tool_sha256={
                    'materialize_h1_verdict_input.py':'c'*64,'materialize_verdict_input.py':'d'*64})
                helper=dict(id='h1',sector='H1',manifest_sha256='e'*64,cnf_sha256='a'*64,
                            status='materialized',container_absent=True,expected_historical_sha256=historical,
                            runner_sha256='c'*64,validator_sha256='d'*64,tag='fixture',profile=0,
                            table_sha256=r.digest(b'[]\n'),emit={'returncode':0},
                            check={'returncode':0},clauses=2,variables=3)
                prepared=dict(helper,identity_basis='historical' if historical else 'new',generator_commit='b'*40)
                self.write(self.root/'input/receipt.json',helper)
                (self.root/'input/check.log').write_text('MATCH (2 clauses, top 3)\n')
                source={'sha256':'e'*64}
                self.assertEqual(r.check_preparation(case,prepared,self.root,source,config),'a'*64)
                for emission in ({'returncode':1}, {}):
                    failed=dict(helper,emit=emission)
                    self.write(self.root/'input/receipt.json',failed)
                    with self.assertRaisesRegex(ValueError,'emitter did not succeed'):
                        r.check_preparation(case,dict(prepared,emit=emission),self.root,source,config)
                self.write(self.root/'input/receipt.json',helper)
                prepared['cnf_sha256']='f'*64
                with self.assertRaises(ValueError):
                    r.check_preparation(case,prepared,self.root,source,config)

    def test_h5_h7_ordered_duplicate_units(self):
        for sector in ('H5','H7'):
            with self.subTest(sector=sector):
                row=dict(units=[1,1,-2],cnf_bytes=24,variables=3,clauses=2)
                case=dict(id='cube',sector=sector,row=row,cnf_sha256='a'*64)
                source=dict(sha256='e'*64,data=dict(variables=3,cube_clauses=2,
                            generator={'last_change_commit':'b'*40}))
                prepared=dict(id='cube',sector=sector,manifest_sha256='e'*64,cnf_sha256='a'*64,
                              status='materialized',generated=True,units=[1,1,-2],cnf_bytes=24,
                              variables=3,clauses=2,generator_commit='b'*40)
                self.assertEqual(r.check_preparation(case,prepared,self.root,source,{}),'a'*64)
                prepared['units']=[1,-2]
                with self.assertRaisesRegex(ValueError,'Cube identity'):
                    r.check_preparation(case,prepared,self.root,source,{})


if __name__=='__main__':
    unittest.main()
