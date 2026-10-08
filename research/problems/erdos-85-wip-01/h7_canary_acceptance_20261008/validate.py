"""Pure metadata checks for captured canary batches and the STOP transition.

These checks never launch, stop, resume, or delete anything. The caller must
retain authoritative cloud observations and bind their bytes independently.
Synthetic tests or an expected-input ledger grant no real canary credit.
"""
from collections import Counter
from datetime import datetime
import hashlib,json,math,re

def require(condition,message):
    if not condition:raise ValueError(message)
def sha(b):return hashlib.sha256(b).hexdigest()
def key(r):return r['cube'],r['kind'],r['leaf']
def validate_batches(expected,bundles,commit,node,manifest_sha,prefix):
    require(re.fullmatch('[a-f0-9]{40}',commit),'Invalid execution commit')
    require(re.fullmatch('[a-f0-9]{64}',manifest_sha),'Invalid manifest pin')
    require(set(bundles)==set(expected['batches']) and len(bundles)==8,'Canary must contain exactly eight selected batches')
    certified=0;residual=[];checked=[]
    for bid,wanted in expected['batches'].items():
        bundle=bundles[bid];ledger=bundle['ledger'];packed=bundle['packed'];raw=bundle['raw']
        require(ledger['id']==bid and ledger['node']==node and ledger['checkout_head']==commit,'Wrong batch, node or execution commit')
        require(ledger['inputs_json_sha256']==expected['inputs_sha256'] and ledger['manifest_sha256']==manifest_sha,'Wrong input/manifest pins')
        require(ledger['results_sha256']==sha(packed) and ledger['receipts_sha256']==sha(raw),'Result transport hash mismatch')
        require(ledger['results_key'].startswith(prefix+'/results/'+bid+'.'+node+'.') and ledger['results_key'].endswith('.jsonl.zst'),'Wrong result key')
        rows=[json.loads(line) for line in raw.splitlines() if line.strip()]
        want={key(r):r for r in wanted};got=[key(r) for r in rows]
        require(len(got)==len(set(got))==len(want) and set(got)==set(want),'Missing, duplicate or out-of-selection item')
        require(ledger['items']==ledger['ran']==len(rows),'Batch item count mismatch')
        statuses=Counter(r['status'] for r in rows)
        require(ledger['statuses']==dict(statuses) and ledger['certified']==statuses.get('CERTIFIED',0),'Ledger status counts disagree')
        for row in rows:
            w=want[key(row)]
            require(row['batch']==bid and row['schema']=='erdos85-h7-hsb-cert-v1','Wrong receipt scope')
            require(row['depth']==expected['depth'] and row['cap_seconds']==expected['cap_seconds'] and row['binaries']==expected['binaries'],'Wrong parameters or binary pins')
            require(row['cnf_sha256']==row['expected_cnf_sha256']==w['cnf_sha256'] and row['cnf_bytes']==w['cnf_bytes'],'Wrong CNF identity')
            require(row.get('units')==w['units'],'Wrong ordered leaf units')
            solver,checker,proof=row['solver'],row['checker'],row['proof']
            require(checker['heap_mb']==expected['heap_mb'] and 'heap_retry_of' not in row,'Unexpected checker heap/retry')
            require(proof['format']=='cadical binary LRAT' and proof['stored'] is False,'Unexpected proof format/storage contract')
            require(type(proof['bytes']) is int and proof['bytes']>0 and re.fullmatch('[a-f0-9]{64}',proof['sha256']),'Invalid proof receipt')
            for process in (solver,checker):
                for field in ('cpu_seconds','wall_seconds','maxrss'):
                    v=process[field];require(type(v) in (int,float) and math.isfinite(v) and v>=0,'Invalid process metric')
            require(datetime.fromisoformat(row['started_utc'].replace('Z','+00:00'))<=datetime.fromisoformat(row['finished_utc'].replace('Z','+00:00')),'Reversed receipt timestamps')
            if row['status']=='CERTIFIED':
                require(solver['returncode']==20 and solver['unsat_line'] is True and checker['returncode']==0 and checker['verified_line'] is True and checker['failure'] is None and proof['checker_closed_early'] is False,'Certified label without complete solver/checker evidence')
                certified+=1
            else:
                require(row['status'] in ('SOLVER_TIMEOUT','CHECK_HEAP_EXHAUSTED'),'Alarm or unexplained item outcome')
                residual.append({'batch':bid,'leaf':row['leaf'],'status':row['status']})
        want_status='CERTIFIED' if statuses=={'CERTIFIED':len(rows)} else 'INCOMPLETE'
        require(ledger['status']==want_status and ledger['batch_returncode']==(0 if want_status=='CERTIFIED' else 1),'Ledger completion disagrees with receipts')
        require(ledger['not_certified']==[{'leaf':r['leaf'],'status':r['status']} for r in rows if r['status']!='CERTIFIED'],'Residual inventory mismatch')
        checked.append({'batch':bid,'items':len(rows),'certified':statuses.get('CERTIFIED',0)})
    require(certified+len(residual)==386,'Wrong complete canary inventory')
    return {'status':'CANARY_RECEIPTS_PASS' if not residual else 'CANARY_RESIDUAL_REVIEW_REQUIRED','certified_items':certified,'residual':residual,'batches':checked,'full_campaign_verified':False,'lean_verified':False}

def validate_transition(observation,node,fleet):
    require(observation['canary_instance_id']==node and observation['canary_fleet_id']==fleet,'Wrong canary cloud identities')
    require(observation['instance_state']=='terminated','Canary node is not terminal')
    inactive=observation['fleet_state'] in ('deleted','deleted_terminating','expired')
    fulfilled_request=(observation.get('fleet_type')=='request' and observation['fleet_state']=='active'
                       and observation.get('initial_request_fulfilled') is True)
    require(inactive or fulfilled_request,'Canary fleet request is not known to be quiescent')
    require(observation['control_keys']==[],'STOP or ALARM remains; classify it before any full-run transition')
    require(observation['live_campaign_instances']==[],'A campaign instance remains live')
    require(observation['controller_hard_stop_usd']==160,'Wrong approved controller limit')
    require(observation['full_manifest_selected'] is True,'Canary-only selection remains in the proposed full configuration')
    require(observation['canary_receipts_reconciled'] is True,'Canary receipts not reconciled')
    require(observation['partial_receipt_path_observed'] is True,'Partial upload path was not observed')
    require(observation['bootstrap_selftests_passed'] is True,'Missing bootstrap checker selftests')
    return {'status':'CANARY_TRANSITION_OBSERVATIONS_PASS','cloud_mutated':False,'full_campaign_verified':False}
