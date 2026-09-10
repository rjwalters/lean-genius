import pathlib,json,hashlib,math
P=pathlib.Path('/tmp/erdos85-sol1-h7-max-high-cover');O=pathlib.Path(__file__).parent;S=pathlib.Path('/tmp/erdos85-sol1-h7-host-profiles/results.json');pins=json.loads((P/'pins.json').read_text());assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items());r=json.loads((P/'results.json').read_text());assert hashlib.sha256(S.read_bytes()).hexdigest()==r['source_sha256'];profiles=json.loads(S.read_text())['results'];out=[]
for a in [6,7,8,9]:
 d=next(x for x in range(7) if 7*x>=4*a);keys=[]
 for family in profiles:
  for i,p in enumerate(family['representatives']):
   if 7-sum(p['empty_counts'][:2])>=d:keys.append([family['twins_adjacent'],i])
 author=next(x for x in r['cases'] if x['empty_edges']==a);assert keys==author['profile_keys'];out.append({'a':a,'minimum_max_degree':d,'keys':keys})
assert list(map(lambda x:len(x['keys']),out))==[16,16,9,2] and out[-1]['keys']==[[True,6],[False,14]]
# Independent labelled isomorphism-type counts for a3edge complement.
c=math.comb
three_edge_types={'triangle':c(7,3),'star':7*c(6,3),'path4':c(7,4)*12,'wedge_plus_edge':7*c(6,2)*c(4,2),'matching3':7*15}
hist={4:three_edge_types['triangle'],3:three_edge_types['star']+three_edge_types['path4'],2:three_edge_types['wedge_plus_edge'],1:three_edge_types['matching3']};assert sum(hist.values())==1330 and hist=={int(k):v for k,v in r['a9_universal_vertex_histogram'].items()}
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
review={'review':2073,'status':'PASS','cases':out,'complement_type_counts':three_edge_types,'universal_vertex_histogram':hist,'pins':pins,'semantic_audit':'For lowvertex supportweightw, low degree7-w and BC weight sum7 give pair_count-empty_count=w. At a pairvertex, pairneighbours have mutually disjoint2colour supports, so pair_count<=3 and empty_count<=1. At an emptyvertex pair_count=empty_count. Consequently Q has exactly2aedges. Empty/high BC summed atcolour i yields singleton_empty_incidence_i+degreeQ_i=7. Maximum-degree choice of high0 gives the mean bound. Wholegraph colour relabelling followed by the reviewed high0 stabilizer preserves this choice and singleton-host incidence sum. The retained profiles cover chosen representations; discarded representations are not graph exclusions.','scope':'Necessary maximal-high cover only. At a9 onlytwin6/crossed14 required; eliminating both remains a separate proof join. No H7/Lean/global closure or capped receipt change.'};(O/'REVIEW2073.json').write_text(json.dumps(review,indent=2)+'\n');print('PASS counts16/16/9/2; independent complement-type histogram',hist)
