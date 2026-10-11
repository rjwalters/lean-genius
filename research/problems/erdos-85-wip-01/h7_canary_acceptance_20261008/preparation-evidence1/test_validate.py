"""Tiny synthetic metadata fixtures; no solver, Lean or real canary credit."""
from copy import deepcopy
import json,unittest
from prepare_inputs import INPUT_SHA,LEAF_CUBES,COVER_CUBES,BINS
from validate import sha,validate_batches,validate_transition

COMMIT='a'*40;MANIFEST='b'*64;NODE='i-fixture';PREFIX='sat49/h7hsb-20261008'
def fixture():
    batches={}
    for cube in LEAF_CUBES:
        if cube in COVER_CUBES:batches[cube+'-cover']=[{'cube':cube,'kind':'cover','leaf':None,'cnf_sha256':sha(cube.encode()),'cnf_bytes':10,'units':None}]
        batches[cube+'-b0000']=[{'cube':cube,'kind':'leaf','leaf':i,'cnf_sha256':sha(f'{cube}:{i}'.encode()),'cnf_bytes':12,'units':[i+1]} for i in range(64)]
    expected={'inputs_sha256':INPUT_SHA,'binaries':BINS,'depth':3,'cap_seconds':7200,'heap_mb':2000,'batches':batches}
    bundles={}
    for bid,wanted in batches.items():
        rows=[]
        for w in wanted:
            rows.append(dict(w,schema='erdos85-h7-hsb-cert-v1',batch=bid,depth=3,cap_seconds=7200,binaries=dict(BINS),expected_cnf_sha256=w['cnf_sha256'],status='CERTIFIED',started_utc='2026-10-08T10:00:00Z',finished_utc='2026-10-08T10:00:01Z',solver={'returncode':20,'unsat_line':True,'cpu_seconds':0.5,'wall_seconds':1,'maxrss':10},checker={'returncode':0,'verified_line':True,'failure':None,'heap_mb':2000,'cpu_seconds':0.2,'wall_seconds':1,'maxrss':10},proof={'format':'cadical binary LRAT','stored':False,'checker_closed_early':False,'bytes':12,'sha256':'c'*64}))
        raw=''.join(json.dumps(r)+'\n' for r in rows).encode()
        ledger={'id':bid,'node':NODE,'checkout_head':COMMIT,'inputs_json_sha256':INPUT_SHA,'manifest_sha256':MANIFEST,'results_sha256':sha(raw),'receipts_sha256':sha(raw),'results_key':PREFIX+'/results/'+bid+'.'+NODE+'.1.jsonl.zst','items':len(rows),'ran':len(rows),'certified':len(rows),'statuses':{'CERTIFIED':len(rows)},'status':'CERTIFIED','batch_returncode':0,'not_certified':[]}
        bundles[bid]={'ledger':ledger,'packed':raw,'raw':raw}
    return expected,bundles
def change_row(bundles,bid,mutate):
    b=bundles[bid];rows=[json.loads(x) for x in b['raw'].splitlines()];mutate(rows)
    raw=''.join(json.dumps(r)+'\n' for r in rows).encode();b.update(raw=raw,packed=raw)
    b['ledger'].update(results_sha256=sha(raw),receipts_sha256=sha(raw))
def check(e,b):return validate_batches(e,b,COMMIT,NODE,MANIFEST,PREFIX)
class ReceiptTests(unittest.TestCase):
    def setUp(self):self.e,self.b=fixture();self.bid='cube_F6_t14-b0000'
    def test_complete_exact_canary(self):
        r=check(self.e,self.b);self.assertEqual(r['status'],'CANARY_RECEIPTS_PASS');self.assertEqual(r['certified_items'],386);self.assertFalse(r['full_campaign_verified']);self.assertFalse(r['lean_verified'])
    def test_missing_batch(self):
        del self.b[self.bid]
        with self.assertRaisesRegex(ValueError,'eight'):check(self.e,self.b)
    def test_duplicate_leaf_hides_missing(self):
        change_row(self.b,self.bid,lambda rows:rows.__setitem__(1,deepcopy(rows[0])))
        with self.assertRaisesRegex(ValueError,'duplicate'):check(self.e,self.b)
    def test_wrong_formula(self):
        change_row(self.b,self.bid,lambda rows:rows[0].update(cnf_sha256='d'*64))
        with self.assertRaisesRegex(ValueError,'CNF'):check(self.e,self.b)
    def test_unapproved_checker(self):
        change_row(self.b,self.bid,lambda rows:rows[0]['binaries'].update(cake_lpr='d'*64))
        with self.assertRaisesRegex(ValueError,'binary'):check(self.e,self.b)
    def test_checker_zero_exit_without_verified_line(self):
        change_row(self.b,self.bid,lambda rows:rows[0]['checker'].update(verified_line=False))
        with self.assertRaisesRegex(ValueError,'solver/checker'):check(self.e,self.b)
    def test_solver_not_unsat_despite_certified(self):
        change_row(self.b,self.bid,lambda rows:rows[0]['solver'].update(returncode=0))
        with self.assertRaisesRegex(ValueError,'solver/checker'):check(self.e,self.b)
    def test_checker_closed_early(self):
        change_row(self.b,self.bid,lambda rows:rows[0]['proof'].update(checker_closed_early=True))
        with self.assertRaisesRegex(ValueError,'solver/checker'):check(self.e,self.b)
    def test_wrong_execution_commit(self):
        self.b[self.bid]['ledger']['checkout_head']='d'*40
        with self.assertRaisesRegex(ValueError,'execution'):check(self.e,self.b)
    def test_compressed_transport_corruption(self):
        self.b[self.bid]['packed']+=b'x'
        with self.assertRaisesRegex(ValueError,'transport'):check(self.e,self.b)
    def test_timeout_is_review_required_not_acceptance(self):
        def timeout(rows):
            rows[0].update(status='SOLVER_TIMEOUT');rows[0]['solver'].update(returncode=0,unsat_line=False,wall_seconds=7200);rows[0]['checker'].update(verified_line=False)
        change_row(self.b,self.bid,timeout)
        self.b[self.bid]['ledger'].update(status='INCOMPLETE',certified=63,statuses={'CERTIFIED':63,'SOLVER_TIMEOUT':1},batch_returncode=1,not_certified=[{'leaf':0,'status':'SOLVER_TIMEOUT'}])
        r=check(self.e,self.b);self.assertEqual(r['status'],'CANARY_RESIDUAL_REVIEW_REQUIRED');self.assertEqual(r['certified_items'],385)
class TransitionTests(unittest.TestCase):
    def setUp(self):
        self.o={'canary_instance_id':NODE,'canary_fleet_id':'fleet-fixture','instance_state':'terminated','fleet_state':'deleted','control_keys':[],'live_campaign_instances':[],'controller_hard_stop_usd':160,'full_manifest_selected':True,'canary_receipts_reconciled':True,'partial_receipt_path_observed':True,'bootstrap_selftests_passed':True}
    def check(self):return validate_transition(self.o,NODE,'fleet-fixture')
    def test_accepted_observations_do_not_grant_campaign(self):self.assertFalse(self.check()['full_campaign_verified'])
    def test_persistent_stop(self):
        self.o['control_keys']=['control/STOP']
        with self.assertRaisesRegex(ValueError,'STOP'):self.check()
    def test_alarm_cannot_be_cleared_by_new_template(self):
        self.o['control_keys']=['control/ALARM-batch']
        with self.assertRaisesRegex(ValueError,'ALARM'):self.check()
    def test_running_node(self):
        self.o['instance_state']='running'
        with self.assertRaisesRegex(ValueError,'terminal'):self.check()
    def test_active_fleet(self):
        self.o['fleet_state']='active'
        with self.assertRaisesRegex(ValueError,'quiescent'):self.check()
    def test_fulfilled_one_time_request_does_not_need_deletion(self):
        self.o.update(fleet_state='active',fleet_type='request',initial_request_fulfilled=True)
        self.assertEqual(self.check()['status'],'CANARY_TRANSITION_OBSERVATIONS_PASS')
    def test_maintain_fleet_cannot_use_one_time_exception(self):
        self.o.update(fleet_state='active',fleet_type='maintain',initial_request_fulfilled=True)
        with self.assertRaisesRegex(ValueError,'quiescent'):self.check()
    def test_missing_operational_evidence(self):
        for field in ('full_manifest_selected','canary_receipts_reconciled','partial_receipt_path_observed','bootstrap_selftests_passed'):
            with self.subTest(field=field):
                self.o[field]=False
                with self.assertRaises(ValueError):self.check()
                self.o[field]=True
    def test_wrong_budget(self):
        self.o['controller_hard_stop_usd']=260
        with self.assertRaisesRegex(ValueError,'limit'):self.check()
if __name__=='__main__':unittest.main()
