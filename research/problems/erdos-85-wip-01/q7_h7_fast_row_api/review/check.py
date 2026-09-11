import pathlib,json,hashlib,importlib.util,itertools,time
P=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-fast-row-api');O=pathlib.Path(__file__).parent;pins=json.loads((P/'pins.json').read_text());assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items());assert (P/'original.py').read_bytes()==(P.parent/'h7-crossed14-arc/filter.py').read_bytes()
mods=[]
for name in ['original','filter']:
 spec=importlib.util.spec_from_file_location(name,P/(name+'.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);mods.append(m)
cases=[r['adjacency'] for r in json.loads((P.parent/'h7-row-compatibility/domains.json').read_text())['results']]
cases += [r['sample'][0] for r in json.loads(pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-residual-groups/host-samples.json').read_text())['results']]
out=[]
for i,adj in enumerate(cases):
 g=list(map(set,adj));H=g[0];V=set(range(7,49))-H;high=set(range(7));pairs=0
 for u,v in itertools.combinations(V,2):
  assert g[u]==(g[u]&high)|(g[u]&H) and len(g[u]&H)==1
  assert bool(g[u]&g[v])==(bool((g[u]&high)&(g[v]&high)) or bool((g[u]&H)&(g[v]&H)));pairs+=1
 for cap in [0,1000,100000]:
  a,b=[m.check(adj,max_nodes=cap) for m in mods];assert a==b
  if cap==0:assert a['status']=='UNKNOWN'
  out.append({'sample':i,'cap':cap,'status':a['status'],'nodes':a['nodes'],'entire_results_equal':True})
 a,b=[m.check(adj,deadline=time.monotonic()-1) for m in mods];assert a==b and a['status']=='UNKNOWN'
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
r={'review':2079,'status':'PASS','cases':out,'guest_pair_identity_checks':4*561,'expired_deadline_cases':4,'pins':pins,'proof':'Input premises give guest-neighbour set=highsupport union singletonhost. Distinct DFSgroups ensure distinct hosts; subset-of-left then XOR ensures pairwise disjoint high supports. Removed intersection predicate is therefore always true on reachable choices. Existing graph immutable, so precomputed common-neighbour limits exactly equal previous expression. Both edits leave branching order/ticks/domains/events identical under a node budget; wall clock stopping times may differ.','scope':'API equivalence only; no new profile/exclusion or retry of a capped research case. Four already terminal fixed examples tested, including intentional budget-control tests.'};(O/'REVIEW2079.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS4samples x3nodecaps,4expired deadlines,2244pair identities')
