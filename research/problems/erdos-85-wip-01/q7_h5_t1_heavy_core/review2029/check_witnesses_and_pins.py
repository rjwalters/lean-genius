import json,pathlib,hashlib,itertools,math
P=pathlib.Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h5_t1_heavy_core')
def sha(b):return hashlib.sha256(b).hexdigest()
pins=json.loads((P/'singleton-tail-pins.json').read_text())
for f,h in pins.items():assert sha((P/f).read_bytes())==h,f
source=json.loads((P/'results.json').read_text());joint=json.loads((P/'joint-results.json').read_text());pilot=json.loads((P/'singleton-tail-results.json').read_text());assert pilot['source_sha256']==sha((P/'results.json').read_bytes())==joint['source_sha256']
selected=sorted((r for r in joint['rows'] if r['status']=='PASS'),key=lambda r:math.prod(r['domain_sizes']))[30:]
assert pilot['selected_core_indices']==[r['core_index'] for r in selected]==[r['core_index'] for r in pilot['rows']]
assert pilot['processed']==181 and pilot['counts']=={'PASS':8,'REJECT':173,'UNKNOWN':0}
supports=source['supports']+[[c] for c in range(5) for _ in range(source['singleton_hosts_by_colour'][c])];supports+=[[]]*(44-len(supports));assert supports[:8]==[[0,1,2],[0,3],[0,4],[1,3],[1,4],[2,3],[2,4],[3,4]]
checked=[]
for r in pilot['rows']:
 assert r['labelled_count']==source['survivors'][r['core_index']]['labelled_count']
 if r['status']!='PASS':continue
 G=[set() for _ in range(49)]
 for u,v in r['partial_graph_edges']:
  assert 0<=u<v<49 and v not in G[u];G[u].add(v);G[v].add(u)
 for c in range(5):assert len(G[c])==8 and not G[c]&set(range(5))
 for v,s in enumerate(supports,5):
  assert G[v]&set(range(5))==set(s) and len(G[v])<=7
  if s:
   for c in range(5):assert len(G[v]&G[c])==1
  else:assert not G[v]
 for u,v in itertools.combinations(range(49),2):assert len(G[u]&G[v])<=1
 assert [[u,v] for u,v in itertools.combinations(range(8),2) if v+5 in G[u+5]]==source['survivors'][r['core_index']]['edges']
 checked.append(dict(core_index=r['core_index'],edges=len(r['partial_graph_edges']),nonempty_BC_rows=31))
for f in ['results.json','joint-results.json','singleton-tail-pins.json']:pins[f]=sha((P/f).read_bytes())
pathlib.Path('witnesses-and-pins.json').write_text(json.dumps(dict(pins=pins,positive_checks=checked,selection_verified=True),indent=2)+'\n');print(checked)
