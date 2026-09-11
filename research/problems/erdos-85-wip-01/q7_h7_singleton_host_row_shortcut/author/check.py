import pathlib,json,itertools,importlib.util,time
from compact import prepare,evaluate
P=pathlib.Path(__file__).parent;A=P.parent/'h7-singleton-complete-row-api';spec=importlib.util.spec_from_file_location('reference',A/'filter.py');ref=importlib.util.module_from_spec(spec);spec.loader.exec_module(ref)
def pairings(xs):
 if not xs:yield ();return
 for j in range(1,len(xs)):
  for rest in pairings(xs[1:j]+xs[j+1:]):yield ((xs[0],xs[j]),)+rest

def singleton_rows(adjacency):
 gm,support,E,U=ref.validate(adjacency);g=list(map(set,adjacency));E=set(E);S=[v for v in U if support[v].bit_count()==1];pp={tuple(i for i in range(7) if support[v]>>i&1):v for v in U if support[v].bit_count()==2};host={v:next(iter(g[v]&E),None) for v in pp.values()};out={};tried=0
 for s in S:
  missing=[h for h in range(7) if not g[s]&g[h]];B=set()
  for e in g[s]&E:B|=g[e]&E
  for t in g[s]&set(S):B|=g[t]&E
  rows=[];count=0
  for matching in pairings(missing):
   count+=1;tried+=1;vs=[pp[e] for e in matching];hs=[host[v] for v in vs if host[v] is not None]
   if len(hs)==len(set(hs)) and not set(hs)&B:rows.append(sum(1<<v for v in vs))
  assert count=={4:3,6:15}[len(missing)];out[s]=rows
 return out,tried
if __name__=='__main__':
 fixtures=json.loads((A/'fixtures.json').read_text());out=[];start=time.monotonic()
 for i,adj in enumerate(fixtures):
  rows,tried=singleton_rows(adj);g,sp,E,U=ref.validate(adj);domains=ref.complete_domains(g,sp,U,ref.Budget(100000,time.monotonic()+60));assert domains['status']=='DOMAINS_COMPLETE'
  fast=evaluate(prepare(adj),{v:sum(1<<e for e in adj[v] if e in E) for v in U if sp[v].bit_count()==2})
  assert fast==rows
  for s,rs in rows.items():assert set(rs)==set(domains['initial'][s])
  out.append(dict(index=i,tried=tried,rows=sum(map(len,rows.values())),negative=any(not rs for rs in rows.values())))
 r=dict(status='PASS',fixtures=len(out),domains=14*len(out),rows=sum(x['rows'] for x in out),negative=sum(x['negative'] for x in out),seconds=time.monotonic()-start,results=out);(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='results'})
