"""Outer H5 accounting; underlying exclusions are reviewed proof premises."""
import pathlib,json,itertools,re,hashlib,sys,collections
P=pathlib.Path(__file__).parent;load=lambda f:json.loads((P/f).read_text())
for f,o in load('origins.json').items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==o['sha256']
if len(sys.argv)>1:
 root=pathlib.Path(sys.argv[1])
 for f,h in load('source-pins.json').items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h,f
reviews={r['id']:r for r in load('reviews.json')};assert set(reviews)=={2022,2032,2037,2062,2063}
assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in reviews.values())
triples=[sum(1<<v for v in c) for c in itertools.combinations(range(5),3)];perms=list(itertools.permutations(range(5)));systems=[];canonical=set()
for code in range(1024):
 selected=[m for i,m in enumerate(triples) if code>>i&1]
 if any((a&b).bit_count()>1 for a,b in itertools.combinations(selected,2)):continue
 systems.append(selected)
 canonical.add(min(tuple(sorted(sum(1<<p[c] for c in range(5) if m>>c&1) for m in selected)) for p in perms))
assert canonical=={(),(7,),(7,25)} and collections.Counter(map(len,systems))=={0:1,1:10,2:15}
lean=(P/'canonical-masks.lean').read_text();families=[]
for t,tr in enumerate([[],[7],[7,25]]):
 pairs=[sum(1<<v for v in c) for c in itertools.combinations(range(5),2) if not any(all(m>>v&1 for v in c) for m in tr)]
 heavy=tr+pairs;singles=[1<<c for c in range(5) for _ in range(4+sum(m>>c&1 for m in tr))];expected=[0]*5+heavy+singles+[0]*(14-t)
 literal=re.search(r'def orderFortyNineFiveHighT'+str(t)+r'Masks\s*: Array Nat :=\s*#\[([^]]+)\]',lean,re.S).group(1);actual=[int(x) for x in re.findall(r'\d+',literal)]
 assert actual==expected and len(actual)==49
 core=load('core-t'+str(t)+'.json');assert core['masks']==heavy and core['complete'] and core['stop'] is None
 counts=[sum(m.bit_count()==w for m in actual[5:]) for w in range(4)];assert counts==[14-t,20+3*t,10-3*t,t]
 families.append(dict(family='T'+str(t),low_support_counts=counts,heavy_core_classes=len(core['canonical_cores']),canonical_49_masks_exact=True))
assert [r['heavy_core_classes'] for r in families]==[1665,249,13]
t0=load('t0-chain.json');assert t0['uncovered_domain']==[] and t0['host_excluded']+t0['host_positive']==1665 and t0['singleton_excluded']+t0['singleton_positive']==t0['host_positive'] and t0['empty_excluded']+1==t0['singleton_positive'] and t0['preserved_search_unknown']==[t0['independent_counting_argument_core']]
t1=load('t1-chain.json');assert t1['status']=='PASS' and t1['remaining_cores']==0 and t1['chain']['heavy_domain']==249 and t1['chain']['singleton_exhausted']+t1['chain']['remaining_empty_exhausted']==t1['chain']['joint_feasible']==211 and t1['chain']['disjoint_complete_chain']
t2=load('t2-chain.json');assert t2['status']=='PASS' and t2['remaining']==[44] and t2['canonical_cores']==load('core-t2.json')['canonical_cores']
left=set(t2['canonical_cores'])
for stage in t2['stages']:
 assert sorted(left)==stage['before'] and set(stage['excluded'])<=left;left-=set(stage['excluded']);assert sorted(left)==stage['after']
assert left=={44}
c44=load('core44-chain.json');assert c44['status']=='PASS' and c44['universe']==len(c44['rows'])==92 and c44['uncovered']==c44['multiply_assigned']==0
assert len({json.dumps(r['key']) for r in c44['rows']})==92
assert c44['no_sharing']+c44['shared_f1']+c44['shared_f2']==92
cover=(P/'canonical-cover.lean').read_text()
for name in ['fiveHighCanonicalLabelingCover_zero','fiveHighCanonicalLabelingCover_one','fiveHighCanonicalLabelingCover_two','orderFortyNineStratumExcluded_five_of_booleanExclusions']:assert 'theorem '+name in cover
out=dict(status='PAPER_AND_FINITE_COMPUTATION_H5_EXCLUDED',premises='Reviewed q7/H5 graph/support/block reduction and accepted exclusion reviews; source-level Lean cover inspection only',families=families,triple_systems=dict(labelled=26,by_size=[1,10,15],canonical=3),family_reviews={'T0':[2037],'T1':[2032],'T2':[2062,2063]},remaining_families=[],source_files=len(load('source-pins.json')),formal_status='Three canonical Boolean-exclusion premises remain undischarged in Lean; no fresh Lean compilation or kernel closure',campaign_status='No SAT queue or historical cap status changed',global_status='H1/H7 and general Erdos85 not resolved by this result')
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
