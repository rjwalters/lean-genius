"""Collect one exact H5 terminal job without executing Lean or changing the peer tree."""
import argparse,base64,hashlib,json,shlex,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='terminal-evidence1');args=parser.parse_args()
    assert Path(args.output).name==args.output and args.output not in ('.','..')
    inventory_data=(ROOT.parent/'h5_stratum_review_20261008/inventory.json').read_bytes()
    fast_data=(ROOT.parent/'h5_fast_review_20261008/evidence/AUDIT.json').read_bytes()
    engine_data=(ROOT.parent/'h5_engine_review_20261008/evidence/AUDIT.json').read_bytes()
    fast=json.loads(fast_data);engine=json.loads(engine_data)
    assert fast['status']=='H5_FAST_LINK_BUILD_AUDIT_PASS'
    assert engine['status']=='CONDITIONAL_SPLIT_CHAIN_BUILD_AUDIT_PASS'
    for old in fast['prerequisites']:
        entry=next(x for x in engine['results'] if x['module']==old['module'])
        assert (old['source_sha256'],old['olean_sha256'])==(entry['source_sha256'],entry['olean_sha256'])
    prerequisites=engine['results']+fast['results']
    assert {p['module'] for p in prerequisites}=={'Erdos85H3PairEngine','Erdos85H5Engine','Erdos85H5Bridge','Erdos85H5Fast'}
    config={'inventory':json.loads(inventory_data),'graph_review':json.loads((ROOT/'graph-axioms.json').read_text()),'prerequisites':prerequisites}
    assert config['graph_review']['execution_commit']==config['inventory']['execution_commit']
    validator=(ROOT/'validate_axioms.py').read_bytes();auditor=(ROOT/'audit_cloud.py').read_bytes()
    code='import types,sys\nm=types.ModuleType("validate_axioms");sys.modules[m.__name__]=m\n'
    code+='exec(compile('+repr(validator)+',"validate_axioms.py","exec"),m.__dict__)\n'
    code+='exec(compile('+repr(auditor)+',"audit_cloud.py","exec"))\nmain('+repr(config)+')\n'
    remote='import base64;exec(compile(base64.b64decode('+repr(base64.b64encode(code.encode()).decode())+'),"h5_collector","exec"))'
    result=subprocess.run(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(remote)],capture_output=True)
    if result.returncode:print(result.stderr.decode());raise SystemExit(result.returncode)
    bundle=json.loads(result.stdout)
    if bundle.get('status')=='PENDING':print(json.dumps(bundle));return
    report=bundle['audit'];files={n:base64.b64decode(b) for n,b in bundle['files'].items()}
    for n,b in files.items():assert sha(b)==report['retained_sha256'][n]
    files.update({'inventory.json':inventory_data,'fast-AUDIT.json':fast_data,'engine-AUDIT.json':engine_data,
                  'graph-axioms.json':(ROOT/'graph-axioms.json').read_bytes(),
                  'audit_cloud.py':auditor,'validate_axioms.py':validator,'capture.py':Path(__file__).read_bytes()})
    report['retained_sha256']={n:sha(b) for n,b in files.items()}
    files['AUDIT.json']=(json.dumps(report,indent=2)+'\n').encode()
    for n,b in files.items():
        path=ROOT/args.output/n;path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():assert path.read_bytes()==b,'Refusing to overwrite evidence: '+n
        else:path.write_bytes(b)
    print(report['status']);print(json.dumps(report.get('problems',[]),indent=2))
    if 'axiom_check' in report:
        print(json.dumps(report['axiom_check'],indent=2))
if __name__=='__main__':main()
