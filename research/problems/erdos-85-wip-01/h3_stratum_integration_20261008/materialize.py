"""Materialize the reviewed proof sources only after full triple-cell acceptance."""
import argparse,json
from pathlib import Path
from transfer_pair import ROOT,REPO,sha,validate_triple

def main():
    p=argparse.ArgumentParser();p.add_argument('--triple-audit',type=Path,required=True)
    p.add_argument('--triple-audit-sha',required=True);p.add_argument('--apply',action='store_true');a=p.parse_args()
    spec=json.loads((ROOT/'SOURCE.json').read_text())
    data=a.triple_audit.read_bytes();assert sha(data)==a.triple_audit_sha
    audit=json.loads(data);validate_triple(audit,spec)
    for name,digest in audit['retained_sha256'].items():assert sha((a.triple_audit.parent/name).read_bytes())==digest
    pending=[]
    for module,row in spec['sources'].items():
        src=ROOT/'source-review/Proofs'/(module+'.lean');dst=REPO/'proofs/Proofs'/(module+'.lean')
        data=src.read_bytes();assert sha(data)==row['source_sha256']
        if dst.exists():assert dst.read_bytes()==data,'Refusing changed existing source: '+module
        else:pending.append((dst,data))
    for module,digest in spec['shared_pair_dependency_sources'].items():
        assert sha((REPO/'proofs/Proofs'/(module+'.lean')).read_bytes())==digest
    if a.apply:
        for dst,data in pending:
            with dst.open('xb') as f:f.write(data)
    print(json.dumps({'status':'SOURCES_MATERIALIZED' if a.apply else 'SOURCE_MATERIALIZATION_PREFLIGHT_PASS',
                      'new_sources':len(pending),'scope':'Source integration only; fresh stratum build/audit still required.'}))
if __name__=='__main__':main()
