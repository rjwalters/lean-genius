from pathlib import Path
import itertools as it,json,time,hashlib
start=time.monotonic();p=Path(__file__).resolve().parent;source=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/residual-ten-11123-supports/results.json');graphs=json.loads(source.read_text())['records']
atoms=[[(2*i,2*i+1)] for i in range(3)]+[[(2*i+b,2*j+(b^s)) for b in range(2)] for i,j in it.combinations(range(3),2) for s in range(2)]
matchings=[]
for bits in it.product(range(2),repeat=9):
 edges=[e for atom,take in zip(atoms,bits) if take for e in atom];deg=[0]*6
 for a,b in edges:deg[a]+=1;deg[b]+=1
 if max(deg,default=0)<=1 and deg[2:]==[1]*4:matchings.append(edges)
records=[];tested=0
for gi,g in enumerate(graphs):
 if time.monotonic()-start>30:raise TimeoutError('Original30s aggregate cap')
 R=[set() for _ in range(10)]
 for a,b in g['edges']:R[a].add(b);R[b].add(a)
 configs=[]
 for si,s in enumerate(g['supports']):
  other=sorted(v^1 for v in s);remaining=sorted(set(range(5))-{v//2 for v in s});supports=[s,other]+[[2*i+b] for i in remaining for b in range(2)]
  for mi,matching in enumerate(matchings):
   tested+=1
   if any(sum(len(R[r])-1 for r in supports[i])+sum(len(supports[b if a==i else a])-1 for a,b in matching if i in (a,b))>2 for i in range(6)):continue
   adj=[set(a) for a in R]+[set() for _ in range(7)]
   def edge(a,b):adj[a].add(b);adj[b].add(a)
   for i,ss in enumerate(supports):
    edge(10+i,16)
    for r in ss:edge(10+i,r)
   for a,b in matching:edge(10+a,10+b)
   if any(len(adj[i]&adj[j])>1 for i in range(17) for j in range(i)):continue
   configs.append({'support_index':si,'internal_matching':matching})
 records.append({'graph':gi,'configurations':configs})
result={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'matching_domain':len(matchings),'tested':tested,'input_graphs':len(graphs),'positive_graphs':sum(bool(r['configurations']) for r in records),'configurations':sum(len(r['configurations']) for r in records),'records':records}
(p/'input-pins.json').write_text(json.dumps({str(source):hashlib.sha256(source.read_bytes()).hexdigest()},indent=2)+'\n');(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'}))
