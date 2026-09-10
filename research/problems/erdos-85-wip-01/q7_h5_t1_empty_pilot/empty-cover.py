"""Exact neighbourhood-multicover necessity on ten fixed partial graphs."""
import json,itertools,time,hashlib
from pathlib import Path
p=Path(__file__).parent;raw=(p/'empty-domains.json').read_bytes();src=json.loads(raw);start=time.monotonic();out=[]
for row in src['rows']:
 domains=list(map(set,row['domains']));pairs=[set(itertools.combinations(sorted(d),2)) for d in domains];demand={int(v):n for v,n in row['demand'].items()};nodes=0;limited=False;solution=None
 def dfs(chosen,available,rem):
  global nodes,limited,solution
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:limited=True;return False
  if not any(rem.values()):
   if len(chosen)==13:solution=chosen;return True
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
 out.append({'core_index':row['core_index'],'status':'PASS' if ok else 'UNKNOWN' if limited else 'REJECT_FIXED_PARTIAL','nodes':nodes,'selected_domains':solution})
result={'input_sha256':hashlib.sha256(raw).hexdigest(),'caps':{'nodes_per_partial':100000,'seconds_total':60},'seconds':time.monotonic()-start,'scope':'Fixed saved singleton completions only; alternate completions still open. Pair reuse forbidden; empty-empty edges not assigned.','rows':out};(p/'empty-cover-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
