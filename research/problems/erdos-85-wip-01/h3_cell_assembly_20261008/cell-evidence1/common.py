"""Validate the full cell's frozen inputs and exact printed axiom sets."""
import json,re
from pathlib import Path
from prepare import ROOT,REPO,sha,complete_ledger
def load_inputs(root=ROOT,repo=REPO):
    plan=json.loads((root/'PLAN.json').read_text());raw={}
    for name,entry in plan['inputs'].items():
        data=(repo/entry['path']).read_bytes()
        if sha(data)!=entry['sha256']:raise ValueError('Pinned input changed: '+name)
        raw[name]=data
    names=('manifest','baseline','sample_audit','prefix_audit','sweep_audit','residual_audit')
    data={n:json.loads(raw[n]) for n in names}
    parts=complete_ledger(*(data[n] for n in names))
    if parts!=plan['parts']:raise ValueError('Assembly object ledger differs from independent audits')
    manifest=data['manifest'];prior=json.loads(raw['prerequisite_audit'])
    if plan['math_commit']!=manifest['math_commit'] or prior['execution_commit']!=plan['math_commit']:
        raise ValueError('Wrong math pin')
    if prior['status']!='RUNTIME_HELPERS_CHAIN_BUILD_AUDIT_PASS' or prior['authoritative_exit']!=0:
        raise ValueError('Runtime prerequisite audit missing')
    if len(prior['results'])!=4:raise ValueError('Wrong runtime chain size')
    if plan['cell']!=manifest['cell'] or sha(raw['cell_source'])!=manifest['cell']['source_sha256']:
        raise ValueError('Reviewed cell source changed')
    if plan['limits']!={'workers':1,'cpus':2,'memory_gib':16,'compile_seconds':90,'outer_timeout':'3m'}:
        raise ValueError('Assembly resource cap changed')
    axioms=sorted({'propext','Classical.choice','Quot.sound'}|{r['native_axiom'] for r in manifest['parts']})
    expected={'Erdos85.H3TripleCompletion.'+name:axioms for name in
              ('threeHighCanonicalRepresentativeExcluded_one','orderFortyNineTripleCellExcluded_three_one')}
    if len(axioms)!=387 or plan['expected_exports']!=expected:raise ValueError('Expected cell axiom set changed')
    return plan,manifest,prior,raw
def parse_axioms(raw,expected):
    if re.search(r'\b(sorry|error)\b',raw,re.I):raise ValueError('Compiler error or sorry')
    reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)
    if [name for name,_ in reports]!=list(expected):raise ValueError('Wrong theorem reports')
    result=[]
    for name,body in reports:
        axioms=[a.strip() for a in body.split(',') if a.strip()]
        if len(axioms)!=len(set(axioms)) or set(axioms)!=set(expected[name]):raise ValueError('Wrong cell axiom set')
        result.append({'theorem':name,'axioms':axioms})
    return result
