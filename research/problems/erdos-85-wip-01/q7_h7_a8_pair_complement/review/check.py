import pathlib,json,hashlib,itertools,math
P=pathlib.Path('/tmp/erdos85-sol1-h7-a8-pair-complement');O=pathlib.Path(__file__).parent;pins=json.loads((P/'pins.json').read_text());assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items());r=json.loads((P/'results.json').read_text());edges=list(itertools.combinations(range(7),2));ei={e:i for i,e in enumerate(edges)}
types={'subdivided_star_plus_edge':[(0,1),(0,2),(0,3),(3,4),(5,6)],'star_plus_path3':[(0,1),(0,2),(0,3),(4,5),(5,6)],'path5_plus_edge':[(0,1),(1,2),(2,3),(3,4),(5,6)],'path4_plus_path3':[(0,1),(1,2),(2,3),(4,5),(5,6)],'triangle_plus_two_edges':[(0,1),(1,2),(0,2),(3,4),(5,6)]};universe=set();counts={};orbits={}
for name,es in types.items():
 orbit={sum(1<<ei[tuple(sorted((p[a],p[b])))] for a,b in es) for p in itertools.permutations(range(7))};assert not orbit&universe;universe|=orbit;counts[name]=len(orbit);orbits[name]=orbit
assert counts==dict(zip(types,[1260,420,1260,1260,105])) and len(universe)==4305
valid=set()
for idx in itertools.combinations(range(21),5):
 degree=[0]*7
 for j in idx:
  for v in edges[j]:degree[v]+=1
 if min(degree)>=1 and max(degree)<=3:valid.add(sum(1<<j for j in idx))
assert valid==universe
for c in r['classes']:
 mask=sum(1<<ei[tuple(e)] for e in c['example_edges']);matches=[name for name,orbit in orbits.items() if mask in orbit];assert len(matches)==1 and counts[matches[0]]==c['labelled_count']
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
review={'review':2081,'status':'PASS','labelled_graphs':4305,'orbit_counts':counts,'pins':pins,'method':'Independent full S7 orbit generation from five explicit graphs; orbit sets disjoint and equal every five-edge/no-isolate/maxdegree3 graph. Compared each author representative to its explicit orbit, no component-signature classification imported.','semantic_audit':'BC and degree give pair_count-empty_count=w and pair_count<=3, yielding pairE<=1 and singletonE<=2. Consequently Q has2aedges and s_i+degQ_i=7. Whole twin6/crossed14 exclusions concern fixed-high profiles irrespective of a or max-degree choice, so every s_i=1 is impossible after those reviewed exclusions. Thus2<=s_i<=4 and1<=degR_i<=3. For a8 R has5edges, degree excess3, giving precisely the two degree sequences. Component classification and independent orbit equality exhaust all five shapes.','scope':'Necessary a8 auxiliary complement cover, no exclusion of any shape or remaining H7case; no Lean/global theorem or capped search.'};(O/'REVIEW2081.json').write_text(json.dumps(review,indent=2)+'\n');print('PASS5disjoint explicit orbits cover4305 graphs')
