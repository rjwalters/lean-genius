"""Bind the unchanged H3 stratum source bundle to a complete new cell audit."""
import argparse,json
from pathlib import Path
from transfer_pair import ROOT,REPO,sha,validate_triple,validate_binding
def main():
    p=argparse.ArgumentParser();p.add_argument('--triple-audit',type=Path,required=True);a=p.parse_args()
    path=a.triple_audit.resolve();raw=path.read_bytes();audit=json.loads(raw)
    source=(ROOT/'SOURCE.json').read_bytes();spec=json.loads(source)
    binding={'status':'CELL_ACCEPTANCE_BOUND','source_spec_sha256':sha(source),'triple_audit_path':str(path.relative_to(REPO)),
             'triple_audit_sha256':sha(raw),'job':audit['job'],'execution_commit':audit['execution_commit'],
             'scope':'New accepted 384-part cell producer; original SOURCE.json and failed campaign receipts remain unchanged.'}
    validate_binding(binding,source)
    spec['triple_producer']=binding;validate_triple(audit,spec)
    for name,digest in audit['retained_sha256'].items():
        if sha((path.parent/name).read_bytes())!=digest:raise ValueError('Cell evidence changed: '+name)
    for module,row in spec['sources'].items():
        if sha((ROOT/'source-review/Proofs'/(module+'.lean')).read_bytes())!=row['source_sha256']:
            raise ValueError('Prepared source bundle changed: '+module)
    out=ROOT/'INTEGRATION.json';encoded=(json.dumps(binding,indent=2)+'\n').encode()
    if out.exists():
        if out.read_bytes()!=encoded:raise ValueError('Refusing to replace another cell binding')
    else:
        with out.open('xb') as f:f.write(encoded)
    print('CELL_ACCEPTANCE_BOUND; no object transfer, source materialization or compilation performed.')
if __name__=='__main__':main()
