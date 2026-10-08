"""Pure input and axiom validation shared by the worker and independent collector."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
def sha(data):return hashlib.sha256(data).hexdigest()
def load_inputs(root=ROOT,repo=REPO):
    plan=json.loads((root/'PLAN.json').read_text());inputs={}
    for name,entry in plan['inputs'].items():
        data=(repo/entry['path']).read_bytes()
        if sha(data)!=entry['sha256']:raise ValueError('Pinned input changed: '+name)
        inputs[name]=data
    manifest=json.loads(inputs['manifest']);prior=json.loads(inputs['prerequisite_audit'])
    if plan['math_commit']!=prior['execution_commit']:raise ValueError('Math pin mismatch')
    if [r['residue'] for r in manifest['parts']]!=list(range(384)):raise ValueError('Invalid inventory')
    reused=[p['residue'] for p in plan['reused_parts']]
    if sorted(reused)!=list(range(89))+[162]:raise ValueError('Unexpected reused residues')
    if plan['known_timeouts']!=[89]:raise ValueError('Known timeout coverage mismatch')
    if plan['remaining_residues']!=[r for r in range(384) if r not in reused and r not in plan['known_timeouts']]:raise ValueError('Remaining coverage mismatch')
    if plan['limits']!={'workers':1,'cpus':2,'memory_gib':16,'per_part_seconds':90,'library_seconds':60,'assembly_seconds':90,'worker_seconds':6900,'outer_timeout':'2h','max_outer_cpu_hours':4}:raise ValueError('Resource plan changed')
    accepted=json.loads(inputs['acceptance'])
    if plan['reused_parts']!=accepted['accepted_parts']:raise ValueError('Accepted ledger differs')
    sample=json.loads(inputs['sample_audit']);prefix=json.loads(inputs['prefix_audit'])
    if sample['status']!='SAMPLE_ARTIFACT_AUDIT_PASS' or prefix['status']!='PARTIAL_CAMPAIGN_ARTIFACT_AUDIT':raise ValueError('Wrong producer audits')
    original={r['residue']:r for r in sample['accepted_parts']+prefix['accepted_parts']}
    if len(original)!=90:raise ValueError('Wrong audited coverage')
    for row in plan['reused_parts']:
        item=original[row['residue']]
        if any(row[k]!=item[k] for k in ('module','source_sha256','object_sha256','object_bytes')):raise ValueError('Unaudited reuse')
    return plan,manifest,prior,inputs

def parse_axioms(raw,expected):
    if re.search(r'\b(sorry|error)\b',raw,re.I):raise ValueError('Compiler error or sorry')
    reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)
    if [name for name,_ in reports]!=list(expected):raise ValueError('Wrong theorem reports')
    result=[]
    for name,body in reports:
        axioms=[a.strip() for a in body.split(',') if a.strip()]
        if len(axioms)!=len(set(axioms)) or set(axioms)!=set(expected[name]):raise ValueError('Wrong axiom set: '+name)
        result.append({'theorem':name,'axioms':axioms})
    return result

def part_expectation(row):return {row['theorem']:{'propext','Quot.sound',row['native_axiom']}}
def cell_expectation(manifest):
    axioms={'propext','Quot.sound','Classical.choice'}|{r['native_axiom'] for r in manifest['parts']}
    return {'Erdos85.H3TripleCompletion.'+name:axioms for name in ('threeHighCanonicalRepresentativeExcluded_one','orderFortyNineTripleCellExcluded_three_one')}
