"""Metadata-only preparation from accepted capstone and H3 evidence."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
MODULE='Erdos85OrderFortyNineCapstoneH3'
CAP='order49_capstone_review_20261008/evidence2/AUDIT.json'
H3='h3_stratum_integration_20261008/stratum-evidence1/AUDIT.json'
def sha(b):return hashlib.sha256(b).hexdigest()
def accepted(relative,status):
    path=ROOT.parent/relative;raw=path.read_bytes();a=json.loads(raw)
    assert a['status']==status and a['authoritative_exit']==0
    for n,h in a['retained_sha256'].items():assert sha((path.parent/n).read_bytes())==h,n
    return a,sha(raw)
def inputs():
    cap,ch=accepted(CAP,'CONDITIONAL_CAPSTONE_ARTIFACT_AUDIT_PASS')
    h3,hh=accepted(H3,'H3_STRATUM_ARTIFACT_AUDIT_PASS')
    rows={r['module']:{'source_sha256':r['source_sha256'],'sha256':r['object']['sha256'],'bytes':r['object']['bytes']} for r in cap['results']}
    assert len(rows)==len(cap['results'])==500
    triple=json.loads((ROOT.parent/H3).with_name('RUN.json').read_text())['imported_objects']
    source=json.loads((ROOT.parent/H3).with_name('SOURCE.json').read_text())['sources'][ 'Erdos85H3Stratum']['source_sha256']
    triple={**triple,'Erdos85H3Stratum':{'source_sha256':source,'sha256':h3['object']['sha256'],'bytes':h3['object']['bytes']}}
    assert len(triple)==418 and len(rows.keys()&triple.keys())==28
    for m in rows.keys()&triple.keys():assert rows[m]==triple[m],m
    objects={**rows,**triple};assert len(objects)==890
    supplement=json.loads((ROOT/'supplementary.json').read_text())
    assert supplement['status']=='BASELINE_OBJECT_OBSERVED_REBUILD_REQUIRED'
    assert supplement['module']=='Erdos85OrderFortyNineThreeHighOneFiber'
    assert supplement['module'] not in objects
    objects[supplement['module']]={k:supplement[k] for k in ('source_sha256','sha256','bytes')}
    exports=[]
    for index,count in [(0,601),(2,607),(3,604)]:
        old=cap['exports'][index]
        name=old['theorem'].replace('_of_externalEvidence_threeStratum','_of_h1_h7Evidence').replace('_of_externalEvidence','_of_h1_h7Evidence')
        axioms=sorted(set(old['axioms'])|set(h3['axioms']))
        assert len(axioms)==count and 'sorryAx' not in axioms
        exports.append({'theorem':name,'axioms':axioms})
    return cap,objects,{'capstone':{'path':CAP,'sha256':ch,'job':cap['job'],'execution_commit':cap['execution_commit']},'h3':{'path':H3,'sha256':hh,'job':h3['job'],'execution_commit':h3['execution_commit']}},exports
def closure(repo,module):
    seen={};pending=[module]
    while pending:
        m=pending.pop()
        if m in seen:continue
        data=(repo/'proofs/Proofs'/(m+'.lean')).read_bytes();seen[m]=sha(data)
        for line in data.decode().splitlines():
            if line.startswith('import '):
                pending.extend(x.removeprefix('Proofs.') for x in line.split()[1:] if x.startswith('Proofs.'))
    return seen
def main():
    cap,objects,producers,exports=inputs();copies={}
    for row in cap['results']:
        m=row['module'];relative='proofs/Proofs/'+m+'.lean'
        data=subprocess.check_output(['git','-C',str(REPO),'show',cap['execution_commit']+':'+relative])
        assert sha(data)==row['source_sha256'],m
        p=REPO/relative
        if p.exists():assert p.read_bytes()==data,'Refusing differing source: '+m
        else:copies[p]=data
    for p,data in copies.items():
        with p.open('xb') as f:f.write(data)
    sources=closure(REPO,MODULE)
    assert set(sources)==set(objects)|{MODULE},(set(sources)-set(objects),set(objects)-set(sources))
    for m,row in objects.items():assert sources[m]==row['source_sha256'],m
    manifest={'status':'ACCEPTED_INPUTS_WITH_BASELINE_REBUILD_PREPARED','module':MODULE,'producers':producers,'objects':objects,'sources':sources,'exports':exports,'copied_sources':sorted(p.stem for p in copies),'supplementary_sha256':sha((ROOT/'supplementary.json').read_bytes()),'limits':{'cpus':2,'memory_gib':16,'workers':1,'inner_seconds_each':90,'outer':'4m'}}
    with (ROOT/'PLAN.json').open('x') as f:json.dump(manifest,f,indent=2);f.write('\n')
    print('Sources copied:',len(copies),'Closure:',len(sources),'Imported objects:',len(objects),'Axioms:',[len(x['axioms']) for x in exports])
if __name__=='__main__':main()
