"""Pure residual plan validation; no compilation or cache mutation."""
import hashlib,json,re
from pathlib import Path
from prepare import build_plan
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
def sha(data):return hashlib.sha256(data).hexdigest()
def load_inputs(root=ROOT,repo=REPO):
    plan=json.loads((root/'PLAN.json').read_text());inputs={}
    for name,entry in plan['inputs'].items():
        data=(repo/entry['path']).read_bytes()
        if sha(data)!=entry['sha256']:raise ValueError('Pinned input changed: '+name)
        inputs[name]=data
    baseline=json.loads(inputs['baseline']);sweep=json.loads(inputs['sweep_audit']);manifest=json.loads(inputs['manifest'])
    rebuilt=build_plan(baseline,sweep,manifest,plan['h5_observation'])
    if set(plan)!=set(rebuilt)|{'inputs','h5_observation_sha256'}:raise ValueError('Unexpected plan fields')
    if any(plan[k]!=v for k,v in rebuilt.items()):raise ValueError('Plan does not match independently audited inputs')
    prior=json.loads(inputs['prerequisite_audit'])
    if prior['execution_commit']!=plan['math_commit']:raise ValueError('Prerequisite math pin differs')
    sample=json.loads(inputs['sample_audit']);prefix=json.loads(inputs['prefix_audit'])
    if sample['status']!='SAMPLE_ARTIFACT_AUDIT_PASS' or prefix['status']!='PARTIAL_CAMPAIGN_ARTIFACT_AUDIT':
        raise ValueError('Wrong baseline audits')
    original=sample['accepted_parts']+prefix['accepted_parts']
    if len(original)!=90 or len({r['residue'] for r in original})!=90:raise ValueError('Wrong baseline audit coverage')
    indexed={r['residue']:r for r in original}
    for row in baseline['accepted_parts']:
        if any(row[k]!=indexed[row['residue']][k] for k in ('module','source_sha256','object_sha256','object_bytes')):
            raise ValueError('Baseline object not independently audited')
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
