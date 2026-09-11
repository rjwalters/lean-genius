"""Structural coverage of host receipts; endpoint truth is checked separately."""
import itertools,time

def options(base,E):
 g=list(map(set,base));H=set(range(7));pv={tuple(sorted(g[u]&H)):u for u in range(7,49) if len(g[u]&H)==2};out=[]
 def match(xs):
  if not xs:yield 0;return
  a=xs[-1]
  for b in xs[:-1]:
   for rest in match([x for x in xs if x not in [a,b]]):yield rest|(1<<pv[tuple(sorted((a,b)))])
 for e in E:
  missing=[h for h in range(7) if not g[e]&g[h]]
  assert len(missing)==2*len(g[e]&set(E));out.append(sorted(match(missing)))
 return out

def check(base,receipt,fixed=None,max_nodes=100000,seconds=60):
 E=receipt['empty_vertices'];order=receipt['order'];status=receipt['status'];assert status in ['COMPLETE','UNKNOWN']
 assert E==[u for u in range(7,49) if not set(base[u])&set(range(7))]
 opts=options(base,E)
 if fixed is not None:
  assert len(fixed)==7 and all(m in opt for m,opt in zip(fixed,opts));opts=[[m] for m in fixed]
 # A timeout during preparation can serialize a shorter order but no endpoints.
 if len(order)<7:
  assert status=='UNKNOWN' and not receipt['prunes'] and not receipt['solutions']
  assert len(order)==len(set(order)) and all(0<=i<7 for i in order)
  return dict(status='UNKNOWN',prefixes=0,solutions=0,coverage_proved=False,nodes=0)
 assert sorted(order)==list(range(7));prefixes=set();solutions=set()
 def key(chosen,depth):
  assert len(chosen)==7 and 0<=depth<=7
  active=set(order[:depth]);used=0
  for i,m in enumerate(chosen):
   if i not in active:assert m==0;continue
   assert m in opts[i] and not m&used;used|=m
  return tuple(chosen[i] for i in order[:depth])
 for r in receipt['prunes']:
  p=key(r['chosen'],r['depth']);assert p not in prefixes;prefixes.add(p)
 for chosen in receipt['solutions']:
  p=key(chosen,7);assert p not in solutions;solutions.add(p)
 assert not prefixes&solutions
 for p in prefixes|solutions:
  assert all(p[:j] not in prefixes for j in range(len(p)))
 if status=='UNKNOWN':return dict(status=status,prefixes=len(prefixes),solutions=len(solutions),coverage_proved=False,nodes=0)
 start=time.monotonic();nodes=0;visitedp=set();visiteds=set()
 def visit(path,used):
  nonlocal nodes
  nodes+=1
  if nodes>max_nodes or time.monotonic()-start>seconds:raise TimeoutError('receipt coverage verification cap')
  if path in prefixes:visitedp.add(path);return
  if len(path)==7:
   assert path in solutions,'unaccounted complete host assignment';visiteds.add(path);return
  for m in opts[order[len(path)]]:
   if not m&used:visit(path+(m,),used|m)
 visit((),0)
 assert visitedp==prefixes and visiteds==solutions
 return dict(status=status,prefixes=len(prefixes),solutions=len(solutions),coverage_proved=True,nodes=nodes)
