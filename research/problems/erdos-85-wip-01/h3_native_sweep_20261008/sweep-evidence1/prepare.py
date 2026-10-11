"""Freeze a skip-on-timeout sweep of the unattempted H3 residues; no Lean."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    base=ROOT.parent;old=json.loads((base/'h3_native_campaign_20261008/PLAN.json').read_text())
    inputs=old['inputs'].copy()
    for name,relative in [('acceptance','h3_native_campaign_20261008/ACCEPTANCE.json'),('prefix_audit','h3_native_campaign_20261008/campaign-evidence1/AUDIT.json')]:
        path=base/relative;inputs[name]={'path':str(path.relative_to(REPO)),'sha256':sha(path)}
    acceptance=json.loads((REPO/inputs['acceptance']['path']).read_text())
    audit=json.loads((REPO/inputs['prefix_audit']['path']).read_text())
    assert audit['status']=='PARTIAL_CAMPAIGN_ARTIFACT_AUDIT' and audit['worker_status']=='TIMEOUT'
    assert acceptance['accepted_unique_residues']==list(range(89))+[162]
    remaining=[r for r in range(384) if r not in acceptance['accepted_unique_residues'] and r!=89]
    assert len(remaining)==293
    plan={'status':'PREPARED_NOT_LAUNCHED','math_commit':old['math_commit'],'modulus':384,
          'reused_parts':acceptance['accepted_parts'],'known_timeouts':[89],'remaining_residues':remaining,
          'inputs':inputs,'limits':old['limits'],'attempt_directory':'attempt1',
          'automatic_retry':False,'timeout_policy':'record and skip; preserve any unaccepted object separately',
          'stop_conditions':['non-timeout compiler failure','source/object/axiom drift','STOP','global deadline'],
          'authorization':{'room_message':53044,'sender':'claude-h5','timestamp':'2026-10-08T13:05:14.498Z',
                           'scope':'Same 90-second cap; skip and record timeouts; no retries inside pass; existing builder only.'},
          'scope':'Map and independently accept unattempted 384-way H3 parts. No full cell or stratum verdict from this sweep.'}
    data=(json.dumps(plan,indent=2)+'\n').encode();p=ROOT/'PLAN.json'
    if p.exists():assert p.read_bytes()==data
    else:p.write_bytes(data)
    print('SWEEP_PREPARED: 90 reused, 1 known timeout, 293 unattempted; no execution.')
if __name__=='__main__':main()
