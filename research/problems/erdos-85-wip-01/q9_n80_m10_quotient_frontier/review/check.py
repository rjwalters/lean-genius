import pathlib,json,gzip,itertools,hashlib,collections
p=pathlib.Path('/tmp/erdos85-sol1-q9-n80-m10-quotient');out=pathlib.Path(__file__).parent
for f,h in json.loads((p/'pins.json').read_text()).items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h
profiles=[(a,)+xs for a in range(3) for xs in itertools.product(range(4),repeat=7) if a+sum(xs)==9 and a*a+sum(x*x for x in xs)<=18];assert len(profiles)==1800
roots=sorted({(r[0],)+tuple(sorted(r[1:])) for r in profiles});assert len(roots)==16
counts=collections.Counter();seen=set();receipts=[]
for l in gzip.open(p/'receipts.jsonl.gz','rt'):
 r=json.loads(l)
 if 'matrix' not in r:
  if 'case' in r:receipts.append(r)
  else:summary=r
  continue
 q=r['matrix'];key=tuple(x for row in q for x in row);assert (r['root'],key) not in seen;seen.add((r['root'],key));counts[r['root']]+=1
 assert len(q)==8 and all(len(row)==8 for row in q) and tuple(q[0])==roots[r['root']]
 for i in range(8):
  assert sum(q[i])==9 and 0<=q[i][i]<=2
  for j in range(8):
   assert q[i][j]==q[j][i] and 0<=q[i][j]<=3
   assert sum(q[i][k]*q[k][j] for k in range(8))<=(18 if i==j else 10)
   if i!=j and q[i][i]==q[j][j]==1:assert q[i][j]==0
assert len(receipts)==16
for i,r in enumerate(receipts):assert r['case']==i and r['nodes']==100000 and r['reason']=='nodes' and r['status']=='UNKNOWN' and r['retained']==counts[i]
assert summary['unknown']==16 and summary['visited']==16 and summary['unvisited']==0 and summary['retained']==sum(counts.values())==1998
report={'status':'PASS_RETAINED_ONLY','matrices':1998,'unknown_roots':16,'complete_roots':0,'scope':'Original saved matrices and statuses only; capped search not replayed.'};(out/'results.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
