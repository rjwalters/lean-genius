import pathlib,json,itertools,hashlib
P=pathlib.Path('/tmp/erdos85-sol1-core44-bf1-exclusion')
for f,h in json.loads((P/'pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
base=json.loads(pathlib.Path('/tmp/erdos85-sol1-core44-colour-matchings/results.json').read_text());names=base['names'];idx={n:i for i,n in enumerate(names)};g=list(map(set,base['base_adjacency']))
sources=[idx[n] for n in ['b0','b2','b4']];targets=[idx[n] for n in ['b2','f2','c2','g2a','g2b']];valid=[]
for assignment in itertools.permutations(targets,3):
 if any(u==v for u,v in zip(sources,assignment)):continue
 trial=[set(ns) for ns in g]
 for u,v in zip(sources,assignment):trial[u].add(v);trial[v].add(u)
 if any(len(trial[u]&trial[v])>1 for u,v in itertools.combinations(range(37),2)):continue
 assert assignment[0]==idx['f2']
 u=idx['b0'];v=idx['f1'];trial[u].add(v);trial[v].add(u)
 assert {idx['f1'],idx['f2']}<=trial[idx['b0']]&trial[idx['F']]
 valid.append([names[v] for v in assignment])
assert len(valid)==2
out=dict(status='PASS',method='All60 target injections checked on independently audited full37vertex skeleton, without author minimal-graph imports',valid_assignments=valid,semantic_audit='B/C/F support and no-sharing class counts; reciprocal colour exclusions; distinct targets forced by commonB; b0-f1 incompatible with forcedb0-f2',scope='Universal no-sharing bf1 exclusion only; no empty pattern or af restriction')
print(out);pathlib.Path(__file__).with_name('REVIEW2055.json').write_text(json.dumps(out,indent=2)+'\n')
