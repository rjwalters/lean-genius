import json,hashlib,itertools,time,pathlib
src=pathlib.Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n80-m16-parity')
base=src.parent/'n80-m16-quotient'
out=pathlib.Path(__file__).parent
start=time.monotonic()
for root,pins in [(src,json.loads((src/'pins.json').read_text())),(base,json.loads((src/'input-pins.json').read_text()))]:
 for name,digest in pins.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
qs=[r['matrix'] for r in json.loads((base/'verification.json').read_text())['representatives']]
records=[json.loads(l) for l in (src/'retained.jsonl').read_text().splitlines()]
receipts=json.loads((src/'results.json').read_text())
results=[]
for t,q in enumerate(qs):
 sq=[[sum(q[i][k]*q[k][j] for k in range(5)) for j in range(5)] for i in range(5)]
 norms=[]
 for i in range(5):
  norms.append({9+sum(2*(-1)**r for r in ss) for ss in itertools.chain.from_iterable(itertools.combinations(range(1,8),k) for k in range(8)) if 2*len(ss)==sq[i][i]-9})
 cross={(i,j):{e-o for e in range(9) for o in range(9) if e+o==sq[i][j]} for i in range(5) for j in range(i+1,5)}
 h=[[0]*5 for _ in range(5)]; found=set();nodes=[0]
 edges=[(i,j) for i in range(5) for j in range(i+1,5)]
 def rec(k):
  nodes[0]+=1
  if k==len(edges):
   for i in range(5):
    if sum(x*x for x in h[i]) not in norms[i]:return
   for (i,j),allowed in cross.items():
    if sum(a*b for a,b in zip(h[i],h[j])) not in allowed:return
   found.add(tuple(x for row in h for x in row));return
  i,j=edges[k]
  for value in range(-q[i][j],q[i][j]+1,2):
   h[i][j]=h[j][i]=value
   if j==4:
    if sum(x*x for x in h[i]) not in norms[i]:continue
    if any(sum(a*b for a,b in zip(h[i],h[r])) not in cross[r,i] for r in range(i)):continue
   rec(k+1)
 for diag in itertools.product(*[[-2,2] if q[i][i]==2 else [q[i][i]] for i in range(5)]):
  for i,d in enumerate(diag):h[i][i]=d
  rec(0)
 saved=[tuple(r['matrix']) for r in records if r['type']==t]
 assert len(saved)==len(set(saved)) and found==set(saved),(t,len(found),len(saved))
 rr=receipts[t]; expected=2**sum(q[i][i]==2 for i in range(5))
 for i,j in edges:expected*=q[i][j]+1
 assert rr['status']=='COMPLETE' and rr['tested']==expected and rr['retained']==len(found)
 results.append({'type':t,'matrices':len(found),'recursive_nodes':nodes[0],'original_combinations':expected})
report={'status':'PASS','types':results,'total':sum(r['matrices'] for r in results),'seconds':time.monotonic()-start,'scope':'Independent upper-edge recursion; necessary parity matrices only, no graph lifting.'}
(out/'results.json').write_text(json.dumps(report,indent=2)+'\n')
(out/'input-pins.json').write_text((src/'pins.json').read_text())
print(json.dumps(report))
