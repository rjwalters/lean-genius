"""Assemble the exact imported-object ledger for the final H3 stratum build."""
import json
from pathlib import Path
from transfer_pair import sha,validate_triple,load_spec

def object_ledger(spec,pair,runtime,triple):
    validate_triple(triple,spec)
    if pair['status']!='H3_PAIR_CELL_TERMINAL_AUDIT_PASS':raise ValueError('Pair audit missing')
    if runtime['status']!='RUNTIME_HELPERS_CHAIN_BUILD_AUDIT_PASS':raise ValueError('Runtime audit missing')
    objects={}
    def add(module,source_hash,object_hash,size):
        if module in objects:raise ValueError('Duplicate imported module: '+module)
        if spec['sources'][module]['source_sha256']!=source_hash:raise ValueError('Imported source mismatch: '+module)
        if size<=0:raise ValueError('Empty imported object: '+module)
        objects[module]={'source_sha256':source_hash,'sha256':object_hash,'bytes':size}
    for row in pair['results']:add(row['module'],row['source_sha256'],row['object']['sha256'],row['object']['bytes'])
    for row in runtime['results']:
        expected={'source_sha256':row['source_sha256'],'sha256':row['olean_sha256'],'bytes':row['olean_bytes']}
        if triple['imported_objects'].get(row['module'])!=expected:raise ValueError('Cell runtime dependency differs')
        add(row['module'],row['source_sha256'],row['olean_sha256'],row['olean_bytes'])
    for row in triple['accepted_parts']+[triple['cell']]:
        add(row['module'].split('.')[-1],row['source_sha256'],row['object_sha256'],row['object_bytes'])
    if set(objects)!=set(spec['sources'])-{'Erdos85H3Stratum'} or len(objects)!=417:
        raise ValueError('Incomplete imported object ledger')
    return objects

def load(root,repo,triple_sha,transfer_sha):
    spec=load_spec(root);binding=spec['triple_producer']
    paths={'SOURCE.json':root/'SOURCE.json',
           'INTEGRATION.json':root/'INTEGRATION.json',
           'pair-AUDIT.json':root.parent/'h3_pair_completion_review_20261008/AUDIT.json',
           'runtime-AUDIT.json':root.parent/'h3_phase3_runtime_20261008/build-evidence/AUDIT.json',
           'triple-AUDIT.json':repo/binding['triple_audit_path'],
           'pair-transfer.json':root/'pair-transfer.json'}
    raw={n:p.read_bytes() for n,p in paths.items()};data={n:json.loads(b) for n,b in raw.items()}
    triple=data['triple-AUDIT.json'];transfer=data['pair-transfer.json']
    if triple_sha!=binding['triple_audit_sha256']:raise ValueError('Triple audit differs from explicit binding')
    if sha(raw['triple-AUDIT.json'])!=triple_sha or sha(raw['pair-transfer.json'])!=transfer_sha:
        raise ValueError('Input receipt hash mismatch')
    if sha(raw['pair-AUDIT.json'])!=spec['pair_audit_sha256']:raise ValueError('Pair receipt changed')
    for name,digest in triple['retained_sha256'].items():
        if sha((paths['triple-AUDIT.json'].parent/name).read_bytes())!=digest:raise ValueError('Triple evidence changed: '+name)
    if transfer['status']!='PAIR_OBJECT_TRANSFER_VERIFIED' or transfer['triple_audit_sha256']!=triple_sha:
        raise ValueError('Pair transfer not verified for this triple audit')
    if transfer['pair_audit_sha256']!=spec['pair_audit_sha256']:raise ValueError('Transfer pair audit differs')
    objects=object_ledger(spec,data['pair-AUDIT.json'],data['runtime-AUDIT.json'],triple)
    for module,row in spec['sources'].items():
        if sha((repo/'proofs/Proofs'/(module+'.lean')).read_bytes())!=row['source_sha256']:
            raise ValueError('Materialized source mismatch: '+module)
    for module,digest in spec['shared_pair_dependency_sources'].items():
        if sha((repo/'proofs/Proofs'/(module+'.lean')).read_bytes())!=digest:raise ValueError('Shared source changed: '+module)
    return spec,objects,raw
