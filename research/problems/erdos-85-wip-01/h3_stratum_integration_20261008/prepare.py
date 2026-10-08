"""Prepare exact H3 integration sources and validate pair dependency compatibility.

Only local source and Git metadata work; no Lean computation or object copying.
"""
from pathlib import Path
import hashlib,importlib.util,json,re,subprocess
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
PAIR='85d336bfbfe'
TRIPLE='002fc52979945c83ada35b24c430e6e2103a6797'
def sha(data):return hashlib.sha256(data).hexdigest()
def git(commit,path):return subprocess.check_output(['git','-C',str(REPO),'show',commit+':'+path])
def save(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    if path.exists():assert path.read_bytes()==data,'Refusing changed preparation: '+str(path)
    else:path.write_bytes(data)
def main():
    pair_pin=subprocess.check_output(['git','-C',str(REPO),'rev-parse',PAIR],text=True).strip()
    pair_audit_path=ROOT.parent/'h3_pair_completion_review_20261008/AUDIT.json'
    pair_audit=json.loads(pair_audit_path.read_text());assert pair_audit['status']=='H3_PAIR_CELL_TERMINAL_AUDIT_PASS'
    manifest_path=ROOT.parent/'h3_native_parts_20261008/MANIFEST.json'
    manifest=json.loads(manifest_path.read_text())
    generator_path=ROOT.parent/'h3_native_parts_20261008/prepare.py'
    assert sha(generator_path.read_bytes())==manifest['source_generator_sha256']
    spec=importlib.util.spec_from_file_location('h3_generator',generator_path)
    gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
    sources={}; records={}
    for row in pair_audit['results']:
        module=row['module'];rel='proofs/Proofs/'+module+'.lean';data=git(pair_pin,rel)
        assert sha(data)==row['source_sha256']
        snapshot=ROOT.parent/'h3_pair_completion_review_20261008/evidence/sources'/(module+'.lean')
        assert data==snapshot.read_bytes()
        sources[module]=data;records[module]={'source_sha256':sha(data),'origin':'audited_pair','object':row['object']}
    pair_names=set(sources)
    # Pair imports outside the 28 audited modules must be byte-identical on this
    # branch, so copied objects cannot silently resolve to changed declarations.
    dependency_sources={};todo=list(pair_names)
    seen=set()
    while todo:
        module=todo.pop()
        if module in seen:continue
        seen.add(module);rel='proofs/Proofs/'+module+'.lean'
        data=git(pair_pin,rel)
        if module not in pair_names:
            assert data==git(TRIPLE,rel)==(REPO/rel).read_bytes(),'Shared dependency differs: '+module
            dependency_sources[module]=sha(data)
        for line in re.findall(r'^import (.+)$',data.decode(),re.M):
            for name in line.split():
                if name.startswith('Proofs.'):todo.append(name[len('Proofs.'):])
    for suffix in ('Runtime','Engine','Bridge','Split'):
        module='Erdos85H3TripleCompletion'+suffix;rel='proofs/Proofs/'+module+'.lean'
        data=git(TRIPLE,rel);assert data==(REPO/rel).read_bytes()
        sources[module]=data;records[module]={'source_sha256':sha(data),'origin':'triple_runtime_chain'}
    for row in manifest['parts']:
        module=row['module'].split('.')[-1];data=gen.part_source(row['residue']).encode()
        assert sha(data)==row['source_sha256'];sources[module]=data
        records[module]={'source_sha256':sha(data),'origin':'triple_inventory','residue':row['residue'],'expected_native_axiom':row['native_axiom']}
    cell=gen.cell_source().encode();assert sha(cell)==manifest['cell']['source_sha256']
    sources['Erdos85H3TripleCompletionCell']=cell;records['Erdos85H3TripleCompletionCell']={'source_sha256':sha(cell),'origin':'planned_triple_assembly'}
    stratum=b'''import Proofs.Erdos85H3PairCell
import Proofs.Erdos85H3TripleCompletionCell
import Proofs.Erdos85OrderFortyNineStrataCapstone

/- The two native-backed cells cover the entire three-high stratum. -/
namespace Erdos85
namespace H3

theorem orderFortyNineStratumExcluded_three : OrderFortyNineStratumExcluded 3 :=
  orderFortyNineStratumExcluded_three_of_tripleCells
    H3Pair.orderFortyNineTripleCellExcluded_three_zero
    H3TripleCompletion.orderFortyNineTripleCellExcluded_three_one

end H3
end Erdos85

#print axioms Erdos85.H3.orderFortyNineStratumExcluded_three
'''
    sources['Erdos85H3Stratum']=stratum;records['Erdos85H3Stratum']={'source_sha256':sha(stratum),'origin':'new_stratum_assembly'}
    pair_axioms=set(pair_audit['axiom_exports'][1]['axioms'])
    triple_axioms={r['native_axiom'] for r in manifest['parts']}
    expected=sorted(pair_axioms|triple_axioms)
    assert len(pair_axioms)==27 and len(triple_axioms)==384 and len(expected)==411
    report={'status':'PREPARED_NOT_COMPILED','pair_source_commit':pair_pin,'triple_source_commit':TRIPLE,
            'pair_audit_sha256':sha(pair_audit_path.read_bytes()),'triple_manifest_sha256':sha(manifest_path.read_bytes()),
            'shared_pair_dependency_count':len(dependency_sources),'shared_pair_dependency_sources':dependency_sources,
            'source_count':len(sources),'sources':records,
            'stratum_export':'Erdos85.H3.orderFortyNineStratumExcluded_three','expected_stratum_axioms':expected,
            'required_before_compile':'Independent H3_TRIPLE_CELL_ARTIFACT_AUDIT_PASS for campaign 503105, then verified object transfer/closure into one complete cache.',
            'scope':'Prepared source integration only; no new proof credit. Expected trust is 408 native axioms plus the standard three.'}
    assert len(sources)==418
    for module,data in sources.items():save(ROOT/'source-review/Proofs'/(module+'.lean'),data)
    save(ROOT/'SOURCE.json',(json.dumps(report,indent=2)+'\n').encode())
    print(f'SOURCE_INTEGRATION_PREPARED: 418 modules; {len(dependency_sources)} shared pair dependencies byte-identical; 411 expected stratum axioms.')
if __name__=='__main__':main()
