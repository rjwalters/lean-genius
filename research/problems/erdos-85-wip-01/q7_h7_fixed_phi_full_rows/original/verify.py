from pathlib import Path
import json,itertools,time,hashlib
p=Path(__file__).parent;inputs=json.loads((p/'input.json').read_text());data=json.loads((p/'results.json').read_text());source={r['source_index']:r for r in inputs};assert len(data['results'])==18 and {r['source_index'] for r in data['results']}==set(source)
for f,h in json.loads((p/'input-pins.json').read_text()).items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h

def matchings(xs):
 if not xs:yield [];return
 u=xs[0]
 for j in range(1,len(xs)):
  for rest in matchings(xs[1:j]+xs[j+1:]):yield [(u,xs[j])]+rest
rows=events=failed=templates=0;start=time.monotonic();summaries=[]
for result in data['results']:
 index=result['source_index'];g=list(map(set,source[index]['adjacency']));H=set(range(7));U=[u for u in range(7,49) if g[u]&H];assert len(U)==35;domains={}
 single={h:[u for u in U if g[u]&H=={h}] for h in H};pair={tuple(sorted(g[u]&H)):u for u in U if len(g[u]&H)==2}
 for u in U:
  need=7-len(g[u]);answers=set()
  for pc in itertools.combinations(range(7),2*(7-need)):
   sc=[h for h in range(7) if h not in pc]
   for pm in matchings(list(pc)):
    pairs=[pair[tuple(sorted(e))] for e in pm]
    for ss in itertools.product(*(single[h] for h in sc)):
     templates+=1;row=set(pairs)|set(ss)
     if u in row or row&g[u]:continue
     ns=g[u]|row
     if len(ns)!=7 or any(len(ns&g[h])!=1 for h in H):continue
     if any((g[v]-{u})&(g[w]-{u}) for v,w in itertools.combinations(ns,2)):continue
     answers.add(frozenset(row))
  supplied=[frozenset(v for v in U if mask>>v&1) for mask in result['initial'][str(u)]]
  assert len(supplied)==len(set(supplied)) and answers==set(supplied),(index,u)
  assert all(sum(1<<v for v in row)==mask for row,mask in zip(supplied,result['initial'][str(u)]))
  domains[u]=answers;rows+=len(answers)
 if result['status']=='INFEASIBLE_ROW':assert not domains[result['empty_vertex']]
 else:
  assert result['status']=='INFEASIBLE_ARC'
  for event in result['events']:
   u,v=event['vertex'],event['against'];removed={frozenset(w for w in U if mask>>w&1) for mask in event['removed']};assert u!=v and len(removed)==len(event['removed']) and removed<=domains[u]
   assert all(mask==sum(1<<w for w in U if mask>>w&1) for mask in event['removed'])
   for a in removed:
    for b in domains[v]:assert ((v in a)!=(u in b)) or len((g[u]|a)&(g[v]|b))>1;failed+=1
   domains[u]-=removed;events+=1
  assert not domains[result['empty_vertex']]
 summaries.append({'source_index':index,'status':'VERIFIED'})
out={'status':'PASS','verified':len(summaries),'complete_rows':rows,'explicit_templates':templates,'deletion_batches':events,'failed_supports':failed,'seconds':time.monotonic()-start,'results':summaries,'scope':'Only18fixedbase graphs, no fullQcolouring/R-F/H7closure.'};(p/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='results'})
