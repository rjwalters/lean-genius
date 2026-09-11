import pathlib,json,itertools,hashlib,time,collections,functools,math
p=pathlib.Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n80-m16-order4');out=pathlib.Path(__file__).parent;start=time.monotonic()
for f,h in json.loads((p/'pins.json').read_text()).items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
qs=[r['matrix'] for r in json.loads((p.parent/'n80-m16-quotient/verification.json').read_text())['representatives']]
parity=[json.loads(l) for l in (p.parent/'n80-m16-parity/retained.jsonl').read_text().splitlines()]
cases=json.loads((p/'inputs.json').read_text());assert cases==[dict(source_index=i,**r) for i,r in enumerate(parity) if r['type'] in [0,1,3,4]]
expected=collections.defaultdict(set)
for l in (p/'retained.jsonl').read_text().splitlines():
 r=json.loads(l);v=tuple(complex(*z) for z in r['matrix']);assert v not in expected[r['source_index']];expected[r['source_index']].add(v)
units=(1,1j,-1,-1j)
@functools.lru_cache(None)
def edge(d,h):
 return sorted({sum(units[x%4] for x in ss) for ss in itertools.combinations(range(16),d) if sum((-1)**x for x in ss)==h},key=lambda z:(z.real,z.imag))
# Actual masks build both moments, independently of row constraints.
squares=collections.defaultdict(set)
for mask in range(65536):
 ss=[x for x in range(16) if mask>>x&1];squares[len(ss),sum((-1)**x for x in ss)].add(sum(units[x%4] for x in ss))
diags=collections.defaultdict(set)
for mask in range(128):
 ss=[x for x in range(1,8) if mask>>(x-1)&1];diags[9+2*len(ss),9+2*sum((-1)**x for x in ss)].add(9+2*sum(units[x%4].real for x in ss))
results=[];edges=[(i,j) for i in range(5) for j in range(i+1,5)]
for case in cases:
 q=qs[case['type']];h=[case['matrix'][5*i:5*i+5] for i in range(5)]
 def square(a):return [[sum(a[i][k]*a[k][j] for k in range(5)) for j in range(5)] for i in range(5)]
 q2,h2=square(q),square(h);c=[[0j]*5 for _ in range(5)]
 for i in range(5):
  if q[i][i]<2:c[i][i]=complex(q[i][i])
  else:
   vals={2*units[s%4].real for s in range(1,8) if 16//math.gcd(16,s)>4 and 2*(-1)**s==h[i][i]};assert len(vals)==1;c[i][i]=complex(vals.pop())
 domains=[edge(q[i][j],h[i][j]) for i,j in edges];found=set();nodes=[0]
 def rec(k):
  nodes[0]+=1
  assert nodes[0]<1000000 and time.monotonic()-start<60,'independent audit bound'
  if k==10:
   if sum(z.real*z.real+z.imag*z.imag for z in c[4]) not in diags[q2[4][4],h2[4][4]]:return
   if any(sum(c[4][a]*c[r][a].conjugate() for a in range(5)) not in squares[q2[4][r],h2[4][r]] for r in range(4)):return
   found.add(tuple(z for row in c for z in row));return
  i,j=edges[k]
  for z in domains[k]:
   c[i][j]=complex(z);c[j][i]=complex(z).conjugate()
   if j==4:
    if sum(z.real*z.real+z.imag*z.imag for z in c[i]) not in diags[q2[i][i],h2[i][i]]:continue
    if any(sum(c[i][a]*c[r][a].conjugate() for a in range(5)) not in squares[q2[i][r],h2[i][r]] for r in range(i)):continue
   rec(k+1)
 rec(0);assert found==expected[case['source_index']],case['source_index']
 results.append({'source_index':case['source_index'],'type':case['type'],'retained':len(found),'nodes':nodes[0]})
source=json.loads((p/'results.json').read_text());assert source['status']=='COMPLETE' and source['visited']==180 and not source['unknown'] and source['unvisited']==0
assert [(r['source_index'],r['retained']) for r in source['cases']]==[(r['source_index'],r['retained']) for r in results]
r={'status':'PASS','cases':len(results),'retained':sum(x['retained'] for x in results),'nodes':sum(x['nodes'] for x in results),'max_nodes':max(x['nodes'] for x in results),'seconds':time.monotonic()-start,'results':results};(out/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='results'})
