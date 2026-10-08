"""Inspect/copy audited pair .olean files after successful triple-cell acceptance.

Run on the cloud host. Default is read-only; --apply performs exclusive,
atomic publication of missing files and never overwrites a cache artifact.
"""
import argparse,hashlib,json,os,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
PAIR_CACHE=Path('/var/lib/docker/volumes/lean-build-erdos85__h3-pair-formal-20261008/_data/lib/lean/Proofs')
TRIPLE_CACHE=Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs')
JOB=Path('/opt/e85/jobs/20261008T124453-erdos85__h3-triple-formal-20261007-503105')
def sha(data):return hashlib.sha256(data).hexdigest()
def inspect(rows,source,destination):
    result=[]
    for row in rows:
        name=row['module']+'.olean';src=source/name;dst=destination/name
        data=src.read_bytes();expected=row['object']
        if sha(data)!=expected['sha256'] or len(data)!=expected['bytes']:
            raise ValueError('Audited source object mismatch: '+name)
        if dst.exists() and dst.read_bytes()!=data:
            raise ValueError('Refusing differing destination object: '+name)
        result.append({'module':row['module'],'source_sha256':row['source_sha256'],
                       'object_sha256':sha(data),'object_bytes':len(data),'destination_exists':dst.exists()})
    return result

def publish(rows,source,destination):
    before=inspect(rows,source,destination) # Check the whole batch before any mutation.
    created=[]
    for row in rows:
        name=row['module']+'.olean';src=source/name;dst=destination/name
        data=src.read_bytes();expected=row['object']
        if sha(data)!=expected['sha256'] or len(data)!=expected['bytes']:
            raise ValueError('Source changed before copy: '+name)
        if dst.exists():
            if dst.read_bytes()!=data:raise ValueError('Destination changed: '+name)
            continue
        fd,temp=tempfile.mkstemp(prefix='.h3-pair-transfer-',dir=destination)
        try:
            with os.fdopen(fd,'wb') as f:f.write(data);f.flush();os.fsync(f.fileno())
            try:os.link(temp,dst);created.append(name)
            except FileExistsError:
                if dst.read_bytes()!=data:raise ValueError('Conflicting concurrent destination: '+name)
        finally:Path(temp).unlink(missing_ok=True)
    after=inspect(rows,source,destination)
    if not all(x['destination_exists'] for x in after):raise ValueError('Incomplete object transfer')
    return {'before':before,'after':after,'created':created}

def validate_triple(audit,spec):
    if audit['status']!='H3_TRIPLE_CELL_ARTIFACT_AUDIT_PASS' or audit['authoritative_exit']!=0:
        raise ValueError('Full triple-cell acceptance required')
    if audit['job']!=JOB.name or audit['execution_commit']!=spec['triple_source_commit']:
        raise ValueError('Wrong triple producer')
    residues=audit['reused_residues']+audit['accepted_new_residues']
    if len(residues)!=384 or sorted(residues)!=list(range(384)):
        raise ValueError('Incomplete or duplicate triple coverage')
    if audit['cell']['module']!='Proofs.Erdos85H3TripleCompletionCell':raise ValueError('Wrong cell module')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--triple-audit',type=Path,required=True)
    parser.add_argument('--triple-audit-sha',required=True)
    parser.add_argument('--apply',action='store_true')
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    assert str(REPO).startswith('/opt/e85/wt/'),'Cloud host only'
    assert (JOB/'exit').read_text().strip()=='0','Producer must be terminal and successful'
    pid=int((JOB/'pid').read_text());assert not Path(f'/proc/{pid}').exists(),'Producer PID still exists'
    spec=json.loads((ROOT/'SOURCE.json').read_text())
    pair_path=ROOT.parent/'h3_pair_completion_review_20261008/AUDIT.json'
    assert sha(pair_path.read_bytes())==spec['pair_audit_sha256']
    pair=json.loads(pair_path.read_text());assert pair['status']=='H3_PAIR_CELL_TERMINAL_AUDIT_PASS'
    assert sha(args.triple_audit.read_bytes())==args.triple_audit_sha
    triple=json.loads(args.triple_audit.read_text());validate_triple(triple,spec)
    for name,digest in triple['retained_sha256'].items():
        assert sha((args.triple_audit.parent/name).read_bytes())==digest,'Triple evidence changed: '+name
    for module,digest in spec['shared_pair_dependency_sources'].items():
        assert sha((REPO/'proofs/Proofs'/(module+'.lean')).read_bytes())==digest
    for row in pair['results']:
        data=(ROOT/'source-review/Proofs'/(row['module']+'.lean')).read_bytes()
        assert sha(data)==row['source_sha256']
    # The already accepted triple objects must also remain intact in this cache.
    manifest=json.loads((ROOT.parent/'h3_native_parts_20261008/MANIFEST.json').read_text())
    sample=json.loads((ROOT.parent/'h3_native_parts_20261008/sample-evidence/AUDIT.json').read_text())
    for row in sample['accepted_parts']+triple['accepted_parts']+[triple['cell']]:
        data=(TRIPLE_CACHE/(row['module'].split('.')[-1]+'.olean')).read_bytes()
        assert sha(data)==row['object_sha256'] and len(data)==row['object_bytes']
    assert len(pair['results'])==28 and manifest['modulus']==384
    if args.apply:
        assert args.receipt is not None and not args.receipt.exists(),'New receipt path required'
        result=publish(pair['results'],PAIR_CACHE,TRIPLE_CACHE)
        result.update(status='PAIR_OBJECT_TRANSFER_VERIFIED',pair_audit_sha256=spec['pair_audit_sha256'],
                      triple_audit_sha256=args.triple_audit_sha,scope='Byte-identical object transfer only; no new stratum theorem.')
        with args.receipt.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    else:result={'status':'PAIR_OBJECT_TRANSFER_PREFLIGHT_PASS','objects':inspect(pair['results'],PAIR_CACHE,TRIPLE_CACHE)}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
