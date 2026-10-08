"""Validate the seven H5 exports against exact, separately reviewed trust sets."""
import re
STANDARD={'propext','Classical.choice','Quot.sound'}
def check_reports(log, inventory, graph_review):
    results=[]
    by_cell={c['index']:{p['expected_native_axiom'] for p in c['parts']} for c in inventory['cells']}
    expected=[]
    for c in inventory['cells']:
        expected.append((c['module'],c['representative_export'],by_cell[c['index']],False))
    for i,name in enumerate(inventory['stratum_exports']):
        parts=by_cell[i] if i<3 else set().union(*by_cell.values())
        expected.append(('Erdos85H5Stratum',name,parts,True))
    problems=[]; needs_review=False
    for module,name,parts,graph in expected:
        pattern=r"info: Proofs/"+re.escape(module)+r"\.lean:\d+:\d+: '"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]"
        matches=re.findall(pattern,log)
        if len(matches)!=1:
            problems.append(name+': expected exactly one raw axiom report');continue
        axioms=[x.strip() for x in matches[0].split(',') if x.strip()]
        if len(axioms)!=len(set(axioms)):
            problems.append(name+': duplicate axioms');continue
        actual=set(axioms); required=STANDARD|parts
        extras=actual-required
        row={'theorem':name,'module':module,'axioms':axioms,'required_search_axiom_count':len(parts),
             'additional_graph_axioms':sorted(extras) if graph else []}
        results.append(row)
        if not required<=actual:
            problems.append(name+': missing required logical or search-part axioms')
        if any('sorry' in x.lower() for x in axioms):problems.append(name+': sorry axiom')
        if not graph and actual!=required:problems.append(name+': representative axiom mismatch')
        if graph:
            if graph_review.get('status')!='EXACT_GRAPH_AXIOMS_REVIEWED':
                needs_review=True
            else:
                reviewed=graph_review.get('exports',{}).get(name)
                if reviewed is None or extras!=set(reviewed):
                    problems.append(name+': graph axiom set differs from exact reviewed list')
    return {'status':'REJECTED' if problems else 'NEEDS_GRAPH_AXIOM_REVIEW' if needs_review else 'AXIOM_SETS_PASS',
            'problems':problems,'exports':results}
