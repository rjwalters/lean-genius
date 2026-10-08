"""Collect the existing capstone job without launching or modifying it."""
import argparse,base64,json,shlex,subprocess,zlib
from pathlib import Path
from prepare import ROOT,REPO,sha
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',default='evidence1');a=p.parse_args()
    assert Path(a.output).name==a.output and a.output not in ('.','..')
    source_raw=(ROOT/'SOURCE.json').read_bytes();source=json.loads(source_raw)
    for name,entry in source['inputs'].items():
        data=(REPO/entry['path']).read_bytes();assert sha(data)==entry['sha256']
        assert data==(ROOT/'inputs'/(name+'-AUDIT.json')).read_bytes()
    review_path=ROOT/'axioms.json'
    review_raw=review_path.read_bytes() if review_path.exists() else b'{"status":"AWAITING_PRINTED_SET_REVIEW","exports":{}}\n'
    review=json.loads(review_raw);auditor=(ROOT/'audit_cloud.py').read_bytes()
    owner_sources={}
    if review['status']=='EXACT_AXIOMS_REVIEWED':
        assert review['source_spec_sha256']==sha(source_raw)
        assert review['initial_artifact_audit_sha256']==sha((ROOT/'evidence1/AUDIT.json').read_bytes())
        for row in review['source_owners']:
            name='source-owners/'+row['module']+'.lean';data=(ROOT/name).read_bytes()
            assert sha(data)==row['source_sha256']==source['sources'][row['module']]['source_sha256']
            assert row['reviewed_declaration'] in data.decode()
            owner_sources[name]=data
    code='exec(compile('+repr(auditor)+',"audit_cloud.py","exec"))\nmain('+repr({'source':source,'axioms':review,'source_sha256':sha(source_raw)})+')'
    compressed=zlib.compress(code.encode(),9);assert zlib.decompress(compressed)==code.encode()
    remote='import base64,zlib;exec(compile(zlib.decompress(base64.b64decode('+repr(base64.b64encode(compressed).decode())+')),"capstone_audit","exec"))'
    result=subprocess.run(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(remote)],capture_output=True)
    if result.returncode:print(result.stderr.decode());raise SystemExit(result.returncode)
    bundle=json.loads(result.stdout)
    if bundle.get('status')=='PENDING':print(json.dumps(bundle));return
    audit=bundle['audit'];files={n:base64.b64decode(b) for n,b in bundle['files'].items()}
    for n,b in files.items():assert sha(b)==audit['retained_sha256'][n]
    files.update({'SOURCE.json':source_raw,'axioms.json':review_raw,'auditor.py':auditor,'collector.py':Path(__file__).read_bytes()})
    files.update(owner_sources)
    for name in source['inputs']:files['inputs/'+name+'-AUDIT.json']=(ROOT/'inputs'/(name+'-AUDIT.json')).read_bytes()
    audit['retained_sha256']={n:sha(b) for n,b in files.items()};files['AUDIT.json']=(json.dumps(audit,indent=2)+'\n').encode()
    for n,b in files.items():
        path=ROOT/a.output/n;path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():assert path.read_bytes()==b,'Refusing to overwrite evidence: '+n
        else:
            with path.open('xb') as f:f.write(b)
    print(audit['status']);print('Modules:',len(audit['results']),'audited imports:',audit['audited_reused_objects'])
    for row in audit['exports']:
        print(row['theorem'],len(row['axioms']),'axioms; additional:',row['additional_axioms'])
if __name__=='__main__':main()
