"""Synthetic complete-cell metadata for tests only; never writes an acceptance file."""
import json
from pathlib import Path
def complete_cell_fixture():
    root=Path(__file__).resolve().parent;spec=json.loads((root/'SOURCE.json').read_text())
    spec['triple_producer']={'job':'20261008T235959-erdos85__h3-triple-formal-20261007-999999','execution_commit':'b'*40}
    audit={'status':'H3_TRIPLE_CELL_ARTIFACT_AUDIT_PASS','authoritative_exit':0,**spec['triple_producer'],
           'reused_residues':list(range(384)),'accepted_new_residues':[],'whole_cell_verified':True,'accepted_parts':[]}
    natives=[]
    for r in range(384):
        module=f'Erdos85H3TripleCompletionPart{r:03d}';theorem=f'Erdos85.H3TripleCompletion.triplePart_384_{r:03d}'
        native=theorem+'._native.native_decide.ax_1_1';natives.append(native)
        audit['accepted_parts'].append({'residue':r,'module':'Proofs.'+module,'theorem':theorem,
            'source_sha256':spec['sources'][module]['source_sha256'],'object_sha256':'0'*64,'object_bytes':1,
            'axioms':['propext','Quot.sound',native]})
    module='Erdos85H3TripleCompletionCell';axioms=['propext','Classical.choice','Quot.sound']+natives
    audit['cell']={'module':'Proofs.'+module,'source_sha256':spec['sources'][module]['source_sha256'],
                   'object_sha256':'1'*64,'object_bytes':1,'axiom_exports':[
                       {'theorem':'Erdos85.H3TripleCompletion.'+name,'axioms':list(axioms)} for name in
                       ('threeHighCanonicalRepresentativeExcluded_one','orderFortyNineTripleCellExcluded_three_one')]}
    runtime=json.loads((root.parent/'h3_phase3_runtime_20261008/build-evidence/AUDIT.json').read_text())
    audit['imported_objects']={r['module']:{'source_sha256':r['source_sha256'],'sha256':r['olean_sha256'],'bytes':r['olean_bytes']} for r in runtime['results']}
    return spec,audit
