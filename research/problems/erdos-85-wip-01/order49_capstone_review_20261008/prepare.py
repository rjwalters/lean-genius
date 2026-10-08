"""Pin the conditional capstone source closure and previously audited objects."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
COMMIT='c955257fbd9a4b4aab5e96c90e26cdedb0f74a5c'
JOB='20261008T135640-erdos85__order49-capstone-20261008-546872'
MODULE='Erdos85OrderFortyNineCapstone'
def sha(data):return hashlib.sha256(data).hexdigest()
def git(path):return subprocess.check_output(['git','-C',str(REPO),'show',COMMIT+':'+path])
def main():
    paths={'h5':ROOT.parent/'h5_terminal_review_20261008/terminal-evidence2/AUDIT.json',
           'pair':ROOT.parent/'h3_pair_completion_review_20261008/AUDIT.json',
           'h7':ROOT.parent/'h7_hsb_capstone_review_20261008/audit.json'}
    raw={n:p.read_bytes() for n,p in paths.items()};audits={n:json.loads(b) for n,b in raw.items()}
    assert audits['h5']['status']=='H5_STRATUM_ARTIFACT_AUDIT_PASS'
    assert audits['pair']['status']=='H3_PAIR_CELL_TERMINAL_AUDIT_PASS' and audits['h7']['status']=='PASS'
    pending=[MODULE];sources={};snapshots={}
    while pending:
        module=pending.pop()
        if module in sources:continue
        data=git('proofs/Proofs/'+module+'.lean');snapshots[module]=data
        imported=[]
        for line in re.findall(r'^import\s+([^\n]+)',data.decode(),re.M):
            imported.extend(n[len('Proofs.'):] for n in line.split() if n.startswith('Proofs.'))
        sources[module]={'source_sha256':sha(data),'imports':imported};pending.extend(imported)
    prior={}
    def add(module,source_hash,object_hash,provenance):
        assert module in sources and sources[module]['source_sha256']==source_hash,module
        row={'source_sha256':source_hash,'object_sha256':object_hash}
        if module in prior:assert {k:prior[module][k] for k in row}==row
        else:prior[module]={**row,'audits':[]}
        prior[module]['audits'].append(provenance)
    for section in ('results','prerequisites','graph_modules'):
        for row in audits['h5'][section]:add(row['module'],row['source_sha256'],row['object']['sha256'],'h5')
    for row in audits['pair']['results']:add(row['module'],row['source_sha256'],row['object']['sha256'],'pair')
    for row in audits['h7']['source_object_hashes']:add(row['module'],row['source_sha256'],row['object_sha256'],'h7')
    h5=set(audits['h5']['axiom_check']['exports'][-1]['axioms'])
    h7=set(audits['h7']['exports']['Erdos85.orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence'])
    pair=set(audits['pair']['axiom_exports'][-1]['axioms'])
    assert len(h5)==61 and len(h7)==94 and len(pair)==27
    names=['not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence_threeStratum',
           'not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence',
           'minDegreeForC4_fortyEight_fortyNine_exact_of_externalEvidence',
           'minDegreeForC4_fortyNine_lt_fortyEight_of_externalEvidence']
    exports={'Erdos85.'+n:sorted(h5|h7|(set() if i==0 else pair)) for i,n in enumerate(names)}
    result={'status':'SOURCE_REVIEW_PASS_NOT_COMPILED','execution_commit':COMMIT,'job':JOB,'module':MODULE,
            'sources':sources,'audited_imports':prior,'required_inherited_axioms':exports,
            'exact_axiom_review_status':'AWAITING_PRINTED_SET_REVIEW',
            'inputs':{n:{'path':str(p.relative_to(REPO)),'sha256':sha(raw[n])} for n,p in paths.items()},
            'source_review':{'h1':'All capacity-inventory tables in all five profiles require OneHighFamilyV2CheckedUnsat, containing nonzero clauses and actual CNF UNSAT.',
                             'h7':'All 28 structural cubes require SevenHighT0CanonicalHsbEvidence at one depth, with a checked cover and every generated leaf.',
                             'h3':'Whole stratum 3, or triple cell (3,1) together with the independently accepted pair cell, remains an explicit hypothesis.',
                             'finite_drop':'Exact thresholds and strict drop apply the same conditional nonexistence result to the checked finite witnesses.'},
            'resource_note':'Original job spec says 16 CPUs, 48 GiB, 6 workers, 6 h. Author capped container lean-build-546968 to 8 CPUs at 13:59 UTC; independently observed 8 CPUs/48 GiB at 14:00:06 UTC. Preserve the original spec.',
            'scope':'Conditional capstone only. No completion of H1/H7 evidence or H3 triple exclusion; no unconditional drop claim.'}
    encoded=(json.dumps(result,indent=2)+'\n').encode();out=ROOT/'SOURCE.json'
    if out.exists():assert out.read_bytes()==encoded,'Refusing to overwrite source review'
    else:
        with out.open('xb') as f:f.write(encoded)
    for name,data in {'source-review/'+MODULE+'.lean':snapshots[MODULE],**{'inputs/'+n+'-AUDIT.json':b for n,b in raw.items()}}.items():
        p=ROOT/name;p.parent.mkdir(parents=True,exist_ok=True)
        if p.exists():assert p.read_bytes()==data
        else:
            with p.open('xb') as f:f.write(data)
    print('SOURCE_REVIEW_PASS:',len(sources),'repository modules,',len(prior),'previously audited imported objects; no build credit.')
if __name__=='__main__':main()
