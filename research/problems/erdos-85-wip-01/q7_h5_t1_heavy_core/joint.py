"""Joint five-colour host feasibility; bounded, necessary partial-graph test."""
import json,itertools,time,hashlib
from pathlib import Path
root=Path(__file__).parent
raw=(root/'results.json').read_bytes();source=json.loads(raw)
supports=list(map(set,source['supports']));caps=source['singleton_hosts_by_colour'];start=time.monotonic()
rows=[];nodes=0
for index,row in enumerate(source['survivors']):
 adj=[set() for _ in range(8)]
 for i,j in row['edges']:adj[i].add(j);adj[j].add(i)
 covered=[set().union(*(supports[j] for j in adj[i])) for i in range(8)]
 domains=[]
 for c in range(5):
  needed=tuple(i for i in range(8) if c not in covered[i]);options=[]
  def partitions(todo,bins,pairs):
   if len(bins)>caps[c]:return
   if not todo:options.append((tuple(bins),frozenset(pairs)));return
   i,*rest=todo
   partitions(rest,bins+[(i,)],pairs)
   for j in rest:
    if not supports[i]&supports[j] and not adj[i]&adj[j]:
     partitions([k for k in rest if k!=j],bins+[(i,j)],pairs+[(i,j)])
  partitions(needed,[],[]);domains.append(options)
 order=sorted(range(5),key=lambda c:len(domains[c]));chosen={};local_nodes=0;limited=False
 def search(k,used):
  global nodes,local_nodes,limited
  nodes+=1;local_nodes+=1
  if local_nodes>100000 or time.monotonic()-start>60:limited=True;return False
  if k==5:return True
  c=order[k]
  for bins,pairs in domains[c]:
   if used.isdisjoint(pairs):
    chosen[c]=bins
    if search(k+1,used|pairs):return True
    if limited:return False
  return False
 ok=search(0,frozenset());record={'core_index':index,'core_edges':row['edges'],'labelled_count':row['labelled_count'],'domain_sizes':[len(d) for d in domains],'nodes':local_nodes,'status':'PASS' if ok else 'UNKNOWN' if limited else 'REJECT'}
 if ok:
  graph=[set() for _ in range(49)]
  def edge(a,b):graph[a].add(b);graph[b].add(a)
  for i,s in enumerate(supports):
   for c in s:edge(c,5+i)
  for i,j in row['edges']:edge(5+i,5+j)
  vertex=13;host_bins=[]
  for c in range(5):
   bins=list(chosen[c]);host_bins.append([list(b) for b in bins])
   for k in range(caps[c]):
    edge(c,vertex)
    if k<len(bins):
     for i in bins[k]:edge(5+i,vertex)
    vertex+=1
  assert vertex==36
  assert all(len(graph[i]&graph[j])<=1 for i,j in itertools.combinations(range(49),2))
  for i in range(8):
   assert len(graph[5+i])<=7
   for c in range(5):assert sum(c in graph[j] for j in graph[5+i] if j>=5)==1
  record.update(host_bins_by_colour=host_bins,partial_graph_edges=[[i,j] for i in range(49) for j in sorted(graph[i]) if i<j])
 rows.append(record)
 if limited:break
out={'source_sha256':hashlib.sha256(raw).hexdigest(),'scope':'Necessary joint singleton-host feasibility only; empty and singleton completion edges remain unassigned. No sector exclusion or queue change.','caps':{'nodes_per_core':100000,'seconds_total':60},'nodes':nodes,'seconds':time.monotonic()-start,'input_orbits':len(source['survivors']),'processed_orbits':len(rows),'counts':{s:sum(r['status']==s for r in rows) for s in ['PASS','REJECT','UNKNOWN']},'labelled_counts':{s:sum(r['labelled_count'] for r in rows if r['status']==s) for s in ['PASS','REJECT','UNKNOWN']},'rows':rows}
(root/'joint-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
