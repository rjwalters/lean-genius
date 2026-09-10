"""Join executable replay receipts to independently read input/payload identities."""
from pathlib import Path
import json, hashlib, argparse
ROOT=Path(__file__).resolve().parent
PINS={'native':'bd7eb8052623525814a0a37502b47f05375d9d9dfaf96ddc2fcd858958517cea','lean':'d788911fa2dd728006380c9119cb4f93cc160e30134e13864a7b9e1116f28921'}
def require(ok,message):
    if not ok: raise ValueError(message)
def read(name): return json.loads((ROOT/name).read_text())
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--require-complete',action='store_true');args=parser.parse_args()
    cnfs={r['id']:r for r in read('small-high-current-cnf-join.json')['rows']}
    payloads={r['id']:r for r in read('small-high-local-payload-hashes.json')['rows']}
    metadata={r['id']:r for r in read('small-high-root-metadata.json')['rows']}
    require(len(cnfs)==len(payloads)==270 and set(cnfs)==set(payloads),'expected270 candidate identities')
    receipts=[read('h3-cover-replay/receipt.json')]+read('small-high-cover-replay/receipt.json')['rows']
    for path in sorted((ROOT/'small-high-positive-replay').glob('*/receipt.json')):
        receipts.append(json.loads(path.read_text()))
    seen=set();completed=[];pending=[];failures=[];pins=[]
    for r in receipts:
        tag=r['job'];require(tag in cnfs and tag not in seen,'unknown/duplicate job');seen.add(tag)
        require(cnfs[tag]['matches'] and r['cnf_sha256']==cnfs[tag]['current_cnf_sha256'],'CNF identity mismatch')
        require(payloads[tag]['identity_matches'],'compressed payload identity failed')
        require(r['lrat_sha256']==metadata[tag]['ledger_fields']['lrat_sha256'],'raw LRAT identity mismatch')
        if 'compressed_sha256' in r:require(r['compressed_sha256']==payloads[tag]['actual_sha256'],'compressed receipt mismatch')
        runs={x['name']:x for x in r['runs']};require(len(runs)==len(r['runs']) and set(runs)<=set(PINS),'checker set')
        for name,run in runs.items():require(run['binary_sha256']==PINS[name],'checker drift')
        if len(runs)!=2:pending.append(tag);continue
        ok=all(run.get('exit_code')==0 and ('c VERIFIED' if name=='native' else 'LRAT accepted: true') in run.get('stdout','') for name,run in runs.items())
        (completed if ok else failures).append(tag)
    absent=sorted(set(cnfs)-seen)
    summary={'scope':'Input/payload and two pinned executable replay receipt join; no current-source rebuild, generated theorem, or remote durability claim','expected_candidates':270,'successful_both':len(completed),'incomplete_receipts':pending,'missing_receipts':absent,'failed_or_timed_out':failures,'all_candidates_replayed':len(completed)==270,'accepted_current_stack':None}
    if args.require_complete:require(summary['all_candidates_replayed'],'replay batch incomplete or failed')
    (ROOT/'small-high-replay-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:len(v) if isinstance(v,list) else v for k,v in summary.items()},indent=2))
if __name__=='__main__':main()
