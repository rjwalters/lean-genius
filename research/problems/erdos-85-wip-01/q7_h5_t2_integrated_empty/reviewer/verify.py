"""Bounded exhaustive host/singleton completion pilot. Empty edges omitted."""
import json,itertools,time,hashlib,math
from pathlib import Path
from empty_capacity import feasible
root=Path(__file__).parent
masks=[7,25,10,18,12,20];supports=[{c for c in range(5) if m>>c&1} for m in masks];caps=[8-sum(c in s for s in supports) for c in range(5)]
src={'survivors':{key:{'edges':[[u,v] for i,(u,v) in enumerate(itertools.combinations(range(6),2)) if key>>i&1],'labelled_count':None} for key in [1,2120]}}
raw=json.dumps(src,sort_keys=True).encode();start=time.monotonic();records=[]
selected=[{'core_index':key,'domain_sizes':[]} for key in [1,2120]]
for jr in selected:
 index=jr['core_index'];core=src['survivors'][index];adj=[set() for _ in range(6)]
 for i,j in core['edges']:adj[i].add(j);adj[j].add(i)
 covered=[set().union(*(supports[j] for j in adj[i])) for i in range(6)];domains=[]
 for c in range(5):
  options=[]
  def parts(todo,bins,pairs):
   if len(bins)>caps[c]:return
   if not todo:options.append((bins,frozenset(pairs)));return
   i,*rest=todo;parts(rest,bins+[(i,)],pairs)
   for j in rest:
    if not supports[i]&supports[j] and not adj[i]&adj[j]:parts([k for k in rest if k!=j],bins+[(i,j)],pairs+[(i,j)])
  parts([i for i in range(6) if c not in covered[i]],[],[]);domains.append(options)
 nodes=0;host_count=0;capped=False;witness=None
 def tick():
  global nodes,capped
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:capped=True;return False
  return True
 def complete(chosen):
  global host_count,witness
  host_count+=1;g=[set() for _ in range(49)];colour={}
  def edge(a,b):g[a].add(b);g[b].add(a)
  for i,s in enumerate(supports):
   for c in s:edge(c,5+i)
  for i,j in core['edges']:edge(5+i,5+j)
  v=11
  for c in range(5):
   for k in range(caps[c]):
    colour[v]=c;edge(c,v)
    if k<len(chosen[c]):
     for i in chosen[c][k]:edge(v,5+i)
    v+=1
  missing={v:set(range(5))-set().union(*(supports[j-5] for j in g[v] if 5<=j<11)) for v in colour}
  def allowed(v,w):
   return v!=w and w not in g[v] and len(g[v])<7 and len(g[w])<7 and not any(g[w]&g[x] for x in g[v])
  def dfs():
   if not tick():return False
   best=None
   for v in colour:
    for c in sorted(missing[v]):
     choices=[w for w in colour if colour[w]==c and colour[v] in missing[w] and allowed(v,w)]
     if not choices:return False
     if best is None or len(choices)<len(best[2]):best=(v,c,choices)
   if best is None:return feasible(g,tick)
   v,c,choices=best
   for w in choices:
    edge(v,w);missing[v].remove(c);missing[w].remove(colour[v])
    if dfs():return True
    missing[v].add(c);missing[w].add(colour[v]);g[v].remove(w);g[w].remove(v)
    if capped:return False
   return False
  if dfs():
   assert all(len(g[i]&g[j])<=1 for i,j in itertools.combinations(range(49),2))
   assert all(len(g[v])<=7 for v in range(5,37))
   assert all(sum(c in g[w] for w in g[v] if w>=5)==1 for v in range(5,37) for c in range(5))
   witness=[[i,j] for i in range(49) for j in sorted(g[i]) if i<j];return True
  return False
 order=sorted(range(5),key=lambda c:len(domains[c]));chosen={}
 def hosts(k,used):
  if not tick():return False
  if k==5:return complete(chosen)
  c=order[k]
  for bins,pairs in domains[c]:
   if used.isdisjoint(pairs):
    chosen[c]=bins
    if hosts(k+1,used|pairs):return True
    if capped:return False
  return False
 ok=hosts(0,frozenset());records.append({'core_index':index,'labelled_count':core['labelled_count'],'cartesian_host_bound':math.prod(jr['domain_sizes']),'host_assignments_tested':host_count,'nodes':nodes,'status':'PASS' if ok else 'UNKNOWN' if capped else 'REJECT','partial_graph_edges':witness})
 if time.monotonic()-start>60:break
out={'source_sha256':hashlib.sha256(raw).hexdigest(),'selection':'T2 cores1 and2120 only; previously capped9217 is not replayed.','caps':{'nodes_per_core':100000,'seconds_total':60},'scope':'Exhaustive failures reject only stated core. PASS graphs still lack empty-support vertices and degree completion; no sector exclusion.','selected_core_indices':[r['core_index'] for r in selected],'processed':len(records),'seconds':time.monotonic()-start,'counts':{s:sum(r['status']==s for r in records) for s in ['PASS','REJECT','UNKNOWN']},'rows':records}
(root/'review-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
