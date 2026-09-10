"""Exact-set joins only: does not independently prove the exclusion algorithms."""
import hashlib,json,collections
from pathlib import Path
root=Path(__file__).parent
pins={}
def read(path):
 b=path.read_bytes();pins[str(path.relative_to(root))]=hashlib.sha256(b).hexdigest();return json.loads(b)
def unique(rows):
 by={r['core']:r for r in rows};assert len(by)==len(rows);return by
for folder in ['t0-singleton-pilot','t0-singleton-tail','t0-empty-completion','t0-independent-empty','t0-final-capacity']:
 for name,h in read(root/folder/'PINS.json').items():assert hashlib.sha256((root/folder/name).read_bytes()).hexdigest()==h,(folder,name)
base=root/'t0-singleton-pilot';core=read(base/'core-t0.json');hosts=read(base/'hosts-t0.json');universe=set(core['canonical_cores']);assert len(universe)==1665
for f in ['core-t0.json','hosts-t0.json']:
 assert (base/f).read_bytes()==(root.parent/'q7_h5_heavy_core'/f).read_bytes()
for folder in ['t0-singleton-tail','t0-empty-completion','t0-independent-empty']:
 assert (base/'core-t0.json').read_bytes()==(root/folder/'core-t0.json').read_bytes()
hr=unique(hosts['results']);assert set(hr)==universe and hosts['unvisited']==0
host_positive={k for k,r in hr.items() if r['status']=='PARTIAL_WITNESS'};assert len(host_positive)==761
assert collections.Counter(r['status'] for r in hr.values())=={'EXCLUDED_HOST_CAPACITY':407,'EXCLUDED_JOINT_HOSTS':497,'PARTIAL_WITNESS':761}
single_rows=[]
for folder in ['t0-singleton-pilot','t0-singleton-tail']:
 p=root/folder;run=read(p/'singleton-t0.json');assert run['unvisited']==0
 assert run['source_sha256']==pins['t0-singleton-pilot/core-t0.json']
 neg=unique(read(p/'singleton-rejection-audit.json'));by=unique(run['results']);assert set(neg)=={k for k,r in by.items() if r['status']=='EXCLUDED_SINGLETON_COMPLETION'}
 assert all(r['status']=='INDEPENDENTLY_EXHAUSTED' and r['host_assignments']==by[k]['hosts_tried'] for k,r in neg.items())
 single_rows+=run['results']
sr=unique(single_rows);assert set(sr)==host_positive
single_positive={k for k,r in sr.items() if r['status']=='PARTIAL_WITNESS'};assert len(single_positive)==14
assert sum(r['status']=='EXCLUDED_SINGLETON_COMPLETION' for r in sr.values())==747
final=read(root/'t0-empty-completion/empty-t0.json');fr=unique(final['results']);assert set(fr)==single_positive and final['unvisited']==0
assert final['source_sha256']==pins['t0-singleton-pilot/core-t0.json']
negative={k for k,r in fr.items() if r['status']=='EXCLUDED_EMPTY_NECESSITY'};unknown={k for k,r in fr.items() if r['status']=='CAPPED'};assert len(negative)==13 and unknown=={5774048758818}
verification=unique(read(root/'t0-independent-empty/independent-results.json'));assert set(verification)==negative
assert all(r['status']=='INDEPENDENTLY_EXHAUSTED' and r['host_assignments']==fr[k]['hosts_tried'] for k,r in verification.items())
capacity=read(root/'t0-final-capacity/result.json');assert capacity['core'] in unknown and capacity['source_sha256']==pins['t0-singleton-pilot/core-t0.json'];assert capacity['required_heavy_empty_incidence']==20>capacity['available_heavy_empty_incidence_upper_bound']==19
result=dict(core_count=1665,host_excluded=904,host_positive=761,singleton_excluded=747,singleton_positive=14,empty_excluded=13,preserved_search_unknown=sorted(unknown),independent_counting_argument_core=capacity['core'],uncovered_domain=[],review_dependencies=[2022,2025,2031,2033,2034,2036],pins=pins,scope='Exact-set chain and frozen identity validation only. Empty uncovered domain is conditional on mathematical validity of every exclusion; pending reviews are not approved by this audit. No kernel theorem or queue mutation.')
(root/'chain-audit.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='pins'})
