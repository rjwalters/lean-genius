from pathlib import Path
import json,itertools as I,time,functools
p=Path(__file__).parent;b=Path('/tmp/erdos85-sol1-q9-n78-kernel-four-partial-incidences');read=lambda f:json.loads(f.read_text());base=read(b/'results.json');ext=read(b/'extension-results.json');att=read(b/'attachment-results.json');assert all(x['status']=='COMPLETE' for x in [base,ext,att]);els=list(map(tuple,base['elements']));ix={x:i for i,x in enumerate(els)};cosets=base['cosets'];cx={g:i for i,C in enumerate(cosets) for g in C}
def mul(x,y):
 i,j=els[x];k,l=els[y];return ix[(i+(5 if j else 1)*k)%8,j^l]
M=[[mul(x,y) for y in range(16)] for x in range(16)];r4=ix[4,0]
def edge(A,u,v):A[u].add(v);A[v].add(u)
start=time.monotonic();status='INCOMPLETE';records=[]
try:
 for ai,attachment in enumerate(att['records']):
  if attachment['collision'] is not None:continue
  e=ext['records'][attachment['extension_source']];r=base['records'][e['source']];c,d,xp,D=(r[k] for k in ['c','d','xp','D']);delta=attachment['delta'];A=[set() for _ in range(72)];centers={}
  for g,(i,j) in enumerate(els):
   edge(A,8+g,8+M[g][c]);edge(A,cx[g],8+g);edge(A,cx[g],cx[M[g][r4]])
   for v in [cx[M[g][cosets[xp][0]]],8+g,8+M[g][d]]:edge(A,24+g,v)
   for h in D:edge(A,40+g,8+M[g][h])
   for v in [8+g]+[cx[M[g][cosets[x][0]]] for x in e['pair']]:edge(A,56+g,v)
   centers[24+g]=j;centers[40+g]=2+(((i%2)*2+j)^delta);centers[56+g]=2+(i%2)*2+j
  supports={v:sum(1<<x for x in A[v]) for v in range(24,72)};assert all(m.bit_count()==3 for m in supports.values())
  for matching in [1,2,3]:
   tests=[]
   for w in [24,40,56]:
    if time.monotonic()-start>30:raise TimeoutError
    covered=set().union(*({x for x in A[r] if x<24} for r in A[w]));assert len(covered)==9
    target=((1<<24)-1)^sum(1<<r for r in covered);s=centers[w];mate=s^1 if s<2 else 2+((s-2)^matching)
    groups={k:[v for v in range(24,72) if v!=w and centers[v]==k and supports[v]&target==supports[v]] for k in range(6) if k!=mate};order=sorted(groups,key=lambda k:len(groups[k]))
    @functools.lru_cache(None)
    def solve(i,left):
     if time.monotonic()-start>30:raise TimeoutError
     if i==5:return () if left==0 else None
     for v in groups[order[i]]:
      mask=supports[v]
      if left&mask!=mask:continue
      rest=solve(i+1,left^mask)
      if rest is not None:return (v,)+rest
     return None
    witness=solve(0,target)
    tests.append({'origin':w,'target':target,'groups':groups,'witness':witness,'states':solve.cache_info().currsize})
   records.append({'attachment_source':ai,'matching':matching,'tests':tests,'positive':all(t['witness'] is not None for t in tests)})
 status='COMPLETE'
except TimeoutError:pass
out={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':records};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':status,'seconds':out['seconds'],'cases':len(records),'positive':sum(r['positive'] for r in records),'local_checks':sum(len(r['tests']) for r in records)}))
