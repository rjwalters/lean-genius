"""Cloud-host transfer of accepted capstone objects; refuse all conflicts."""
import argparse,importlib.util,json
from pathlib import Path
from prepare import ROOT,REPO,inputs,closure,sha,MODULE
SPEC=importlib.util.spec_from_file_location('pair_transfer',ROOT.parent/'h3_stratum_integration_20261008/transfer_pair.py')
HELPER=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(HELPER)
SOURCE=Path('/var/lib/docker/volumes/lean-build-erdos85__order49-capstone-20261008/_data/lib/lean/Proofs')
DEST=Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs')
def load():
    p=json.loads((ROOT/'PLAN.json').read_text());cap,objects,producers,exports=inputs()
    assert p['objects']==objects and p['producers']==producers and p['exports']==exports
    assert p['sources']==closure(REPO,MODULE)
    for m,row in objects.items():assert p['sources'][m]==row['source_sha256']
    return p,cap
def main():
    p=argparse.ArgumentParser();p.add_argument('--apply',action='store_true');p.add_argument('--receipt',type=Path);a=p.parse_args()
    assert str(REPO).startswith('/opt/e85/wt/')
    plan,cap=load()
    for producer in plan['producers'].values():
        job=Path('/opt/e85/jobs')/producer['job'];assert (job/'exit').read_text().strip()=='0'
        assert not Path('/proc/'+(job/'pid').read_text().strip()).exists()
    rows=cap['results'];existing=set(r['module'] for r in rows)
    def h3_check():
        for m,row in plan['objects'].items():
            if m not in existing:
                b=(DEST/(m+'.olean')).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes'],m
    h3_check()
    if a.apply:
        assert a.receipt is not None and not a.receipt.exists()
        result=HELPER.publish(rows,SOURCE,DEST);result['status']='CAPSTONE_OBJECT_TRANSFER_VERIFIED'
    else:result={'status':'CAPSTONE_OBJECT_TRANSFER_INSPECTION_PASS','objects':HELPER.inspect(rows,SOURCE,DEST)}
    h3_check();result['plan_sha256']=sha((ROOT/'PLAN.json').read_bytes())
    if a.apply:
        with a.receipt.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
