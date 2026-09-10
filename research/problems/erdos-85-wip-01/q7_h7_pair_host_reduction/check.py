from pathlib import Path
import json,itertools,hashlib,time
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-h7-high0-cover/results.json');d=json.loads(src.read_text());names=d['names'];idx={v:i for i,v in enumerate(names)};edges=list(itertools.combinations(range(1,7),2));out=[];start=time.monotonic()
for seed in d['patterns']:
 g=list(map(set,seed['adjacency']));hosts=list(seed['slot_capacities']);hostids=[idx[v] for v in hosts];support={v:set(g[idx[v]])&set(range(7)) for v in hosts}
 mates={a:b for a,b in seed['local_edges']};mates.update({b:a for a,b in seed['local_edges']})
 available=[set(range(1,7))-support[mates[h]] for h in hosts]
 cap=[seed['slot_capacities'][h] for h in hosts];offset=[len(available[i])-cap[i] for i in range(8)]
 assert sum(offset)==8
 assert all(sum(c in a for a in available)==7 for c in range(1,7))
 lower=offset;upper=[len(a)//2 for a in available];used=[set() for _ in hosts];groups=[[] for _ in hosts];nodes=0
 def dfs(k):
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
  if k==15:return all(lower[i]<=len(groups[i])<=upper[i] for i in range(8))
  a,b=edges[k]
  for i in range(8):
   if len(groups[i])>=upper[i] or not {a,b}<=available[i] or {a,b}&used[i]:continue
   used[i].update([a,b]);groups[i].append((a,b))
   if sum(max(0,lower[j]-len(groups[j])) for j in range(8))<=14-k and dfs(k+1):return True
   groups[i].pop();used[i].difference_update([a,b])
  return False
 try:found=dfs(0);status='SAMPLE' if found else 'EXHAUSTED'
 except TimeoutError:found=False;status='UNKNOWN'
 row=dict(twins_adjacent=seed['twins_adjacent'],status=status,nodes=nodes,hosts=hosts,available_colours=[sorted(a) for a in available],pair_min=lower,pair_max=upper,offsets=offset)
 if found:
  def add(u,v):g[u].add(v);g[v].add(u)
  for i,es in enumerate(groups):
   for a,b in es:add(hostids[i],idx['P'+str(a)+str(b)])
  singleton_slots={c:[i for i in range(8) if c in available[i]-used[i]] for c in range(1,7)}
  assert all(len(x)==2 for x in singleton_slots.values())
  for c,hs in singleton_slots.items():
   for letter,i in zip('ab',hs):add(hostids[i],idx['S'+str(c)+letter])
  emptycounts=[len(groups[i])-offset[i] for i in range(8)];assert sum(emptycounts)==7 and min(emptycounts)>=0
  e=0
  for i,n in enumerate(emptycounts):
   for _ in range(n):add(hostids[i],idx['E'+str(e)]);e+=1
  assert all(len(g[u]&g[v])<=1 for u,v in itertools.combinations(range(49),2))
  assert all(len(g[u]&g[0])==1 for u in range(7,49))
  assert all(len(g[h])==7 for h in hostids)
  row.update(pair_groups=groups,empty_counts=emptycounts,singleton_slots=singleton_slots,adjacency=[sorted(x) for x in g])
 out.append(row);print({k:v for k,v in row.items() if k not in ['adjacency','pair_groups','singleton_slots','available_colours']},flush=True)
(p/'results.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),results=out,scope='Exact H0-host parametrization by properK6 edge assignment; one valid partial perseed only, no colouring census/fullgraph/emptyclass exclusion.'),indent=2)+'\n')
