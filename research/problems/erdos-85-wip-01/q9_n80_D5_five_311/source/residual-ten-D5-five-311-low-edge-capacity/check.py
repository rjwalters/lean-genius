from pathlib import Path
import json,itertools as it,time,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();joint={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records']};flow=json.loads((b/'residual-ten-D5-five-311-nonempty-low-integer/results.json').read_text())['records'];graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def flip(m):return sum(1<<(i^1) for i in range(10) if m>>i&1)
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
for f in flow:
 source=joint[f['root']];ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];rho={v:w for a,z in c['edges'] for v,w in [(a,z),(z,a)]};ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];Hg=graphs[source['packing_root']]['survivors'][source['graph']]['edges'];H=[set() for _ in range(10)]
 for v,w in Hg:H[v].add(w);H[w].add(v)
 covered=[{rho[e] for e in s}|set().union(*(S[w] for w in H[v])) for v,s in enumerate(S)];rec={'root':source['root'],'certificates':[],'survivors':[]};out.append(rec)
 for kept in f['survivors']:
  guard();ai=kept['assignment'];a=source['survivors'][ai];Q=[x for m in a['rows'] for x in (m,flip(m))];lows=[(v,r) for v in range(10) for r in range(10) if r not in covered[v] and not(Q[v]>>r&1)]+[(-1,r) for r in range(10) for _ in range(a['inactive'][r])];assert len(lows)==50;N=[set() for _ in range(70)]
  def edge(v,w):N[v].add(w);N[w].add(v)
  for v,w in c['edges']:edge(v,w)
  for v,s in enumerate(S):
   for r in s:edge(10+v,r)
  for v,w in Hg:edge(10+v,10+w)
  for i,(v,r) in enumerate(lows):
   edge(20+i,r)
   if v>=0:edge(20+i,10+v)
  masks=[sum(1<<z for z in ns) for ns in N];common=[[bool(x&y) for y in masks] for x in masks];assert all((x&y).bit_count()<=1 for x,y in it.combinations(masks,2));targets=[set(range(10))-({rho[r]}|(S[v] if v>=0 else set())) for v,r in lows];allowed=[set() for _ in lows]
  for i,j in it.combinations(range(50),2):
   v,r=lows[i];w,e=lows[j]
   if e not in targets[i] or r not in targets[j]:continue
   x,y=20+i,20+j
   if any(common[x][z] for z in N[y]) or any(common[y][z] for z in N[x]):continue
   allowed[i].add(j);allowed[j].add(i)
  bad=None
  for i,(v,r) in enumerate(lows):
   supports={lows[j][1] for j in allowed[i]};needed=targets[i] if v>=0 else set()
   if not needed<=supports or v<0 and len(supports)<7:
    bad={'kind':'vertex_support_capacity','low':i,'active':v>=0,'available':sorted(supports),'required':sorted(needed),'minimum_degree':6 if v>=0 else 7};break
  if bad:rec['certificates'].append({'assignment':ai,**bad});continue
  for r in range(10):
   if bad:break
   for e in range(r,10):
    left=[i for i,(v,s) in enumerate(lows) if s==r and e in targets[i]];right=[i for i,(v,s) in enumerate(lows) if s==e and r in targets[i]]
    if r==e:
     required={i for i in left if lows[i][0]>=0}
     @functools.lru_cache(None)
     def internal(rem):
      guard()
      if not rem:return True
      v=rem[0];rest=rem[1:]
      if v not in required and internal(rest):return True
      return any(w in allowed[v] and internal(tuple(z for z in rest if z!=w)) for w in rest)
     feasible=internal(tuple(left))
    else:
     required_right=sum(1<<j for j,v in enumerate(right) if lows[v][0]>=0)
     @functools.lru_cache(None)
     def bip(i,used):
      guard()
      if i==len(left):return used&required_right==required_right
      v=left[i]
      if lows[v][0]<0 and bip(i+1,used):return True
      return any(not used>>j&1 and w in allowed[v] and bip(i+1,used|1<<j) for j,w in enumerate(right))
     feasible=bip(0,0)
    if not feasible:bad={'kind':'support_block_matching','pair':[r,e],'left':left,'right':right,'allowed':[[i,sorted(allowed[i]&set(right))] for i in left]};break
  if bad:rec['certificates'].append({'assignment':ai,**bad})
  else:rec['survivors'].append({'assignment':ai,'lows':lows,'allowed_edges':[[i,j] for i in range(50) for j in sorted(allowed[i]) if i<j]})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'negative':sum(len(r['certificates']) for r in out),'assignments':sum(len(r['survivors']) for r in out),'positive_cases':sum(bool(r['survivors']) for r in out),'kinds':{k:sum(c['kind']==k for r in out for c in r['certificates']) for k in ['vertex_support_capacity','support_block_matching']}}))
