"""Exact neighbourhood-multicover necessity on ten fixed partial graphs."""
import json,itertools,time,hashlib
from pathlib import Path
p=Path(__file__).parent;raw=(p/'empty-domains.json').read_bytes();src=json.loads(raw);start=time.monotonic();out=[]
partials={r['core_index']:r for name in ['singleton-results.json','singleton-tail-results.json'] for r in json.loads((p/name).read_text())['rows'] if r['status']=='PASS'}
for row in src['rows']:
 domains=list(map(set,row['domains']));pairs=[set(itertools.combinations(sorted(d),2)) for d in domains];demand={int(v):n for v,n in row['demand'].items()};nodes=0;limited=False;solution=None;covers=0;capacity_failures=0;edge_nodes=0
 def finish(chosen):
  global covers,capacity_failures,edge_nodes,limited
  covers+=1;g=[set() for _ in range(49)]
  def edge(a,b):g[a].add(b);g[b].add(a)
  for a,b in partials[row["core_index"]]["partial_graph_edges"]:edge(a,b)
  for k,d in enumerate(chosen):
   for v in domains[d]:edge(36+k,v)
  assert all(len(g[v])==7 for v in range(5,36))
  assert all(len(g[a]&g[b])<=1 for a,b in itertools.combinations(range(49),2))
  def edges():
   global edge_nodes,limited,capacity_failures
   edge_nodes+=1
   if edge_nodes>100000 or time.monotonic()-start>60:limited=True;return False
   opts=[]
   for v in range(36,49):
    n=7-len(g[v])
    if n:
     cs=[w for w in range(36,49) if w!=v and len(g[w])<7 and w not in g[v] and not any(g[w]&g[x] for x in g[v])]
     if len(cs)<n:capacity_failures+=1;return False
     opts.append((len(cs),v,n,cs))
   if not opts:return True
   _,v,n,cs=min(opts)
   for block in itertools.combinations(cs,n):
    added=[];ok=True
    for w in block:
     if any(g[w]&g[x] for x in g[v]):ok=False;break
     edge(v,w);added.append(w)
    if ok and edges():return True
    for w in added:g[v].remove(w);g[w].remove(v)
    if limited:return False
   return False
  ok=edges()
  if ok:
   assert all(len(g[v])==(8 if v<5 else 7) for v in range(49))
   assert all(len(g[a]&g[b])<=1 for a,b in itertools.combinations(range(49),2))
   (p/"full-graph-candidate.json").write_text(json.dumps([[a,b] for a in range(49) for b in sorted(g[a]) if a<b]))
  return ok
 def dfs(chosen,available,rem):
  global nodes,limited,solution
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:limited=True;return False
  if not any(rem.values()):
   if len(chosen)==13 and finish(chosen):solution=chosen;return True
   return False
  if len(chosen)>=13:return False
  valid=[k for k in available if all(rem[v]>0 for v in domains[k])]
  options=[]
  for v,n in rem.items():
   if n:
    choices=[k for k in valid if v in domains[k]]
    if len(choices)<n:return False
    options.append((len(choices),v,choices))
  _,v,choices=min(options)
  # In every extension exactly rem[v] of these domains must be selected.
  for block in itertools.combinations(choices,rem[v]):
   if len(chosen)+len(block)>13:continue
   used=set();r=rem.copy();ok=True
   for k in block:
    if used & pairs[k]:ok=False;break
    used |= pairs[k]
    for w in domains[k]:
     r[w]-=1
     if r[w]<0:ok=False
   if not ok:continue
   nxt=[k for k in valid if k not in block and not(pairs[k]&used) and v not in domains[k]]
   if dfs(chosen+list(block),nxt,r):return True
   if limited:return False
  return False
 ok=dfs([],list(range(len(domains))),demand)
 out.append({'core_index':row['core_index'],'status':'PASS' if ok else 'UNKNOWN' if limited else 'REJECT_FIXED_PARTIAL','nodes':nodes,'selected_domains':solution,'covers_tested':covers,'empty_edge_nodes':edge_nodes,'capacity_failures':capacity_failures})
result={'input_sha256':hashlib.sha256(raw).hexdigest(),'caps':{'nodes_per_partial':100000,'seconds_total':60},'seconds':time.monotonic()-start,'scope':'Fixed saved singleton completions only; alternate completions still open. All covers and their empty-empty completions checked within caps.','rows':out};(p/'empty-all-cover-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
