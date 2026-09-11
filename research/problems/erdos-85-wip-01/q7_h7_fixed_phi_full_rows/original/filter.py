"""Necessary complete-row/arc filter for high+empty-complete H7 graphs."""
import time
class Limit(Exception):pass
class Budget:
 def __init__(self,max_nodes,deadline):
  if not isinstance(max_nodes,int) or max_nodes<0:raise ValueError('invalid node budget')
  self.nodes=0;self.max_nodes=max_nodes;self.deadline=float('inf') if deadline is None else deadline
 def tick(self):
  self.nodes+=1
  if self.nodes>self.max_nodes or time.monotonic()>self.deadline:raise Limit

def validate(adjacency):
 if len(adjacency)!=49:raise ValueError('need49vertices')
 g=[]
 for u,ns in enumerate(adjacency):
  ns=set(ns)
  if any(not isinstance(v,int) or not 0<=v<49 or v==u for v in ns):raise ValueError('bad edge')
  g.append(ns)
 if any(u not in g[v] for u in range(49) for v in g[u]):raise ValueError('asymmetric')
 H=set(range(7));support=[sum(1<<h for h in g[u]&H) for u in range(49)]
 if any(len(g[h])!=8 or g[h]&H for h in H):raise ValueError('bad highs')
 E=[u for u in range(7,49) if support[u]==0];U=[u for u in range(7,49) if support[u]]
 if len(E)!=7 or len(U)!=35:raise ValueError('bad support counts')
 expected=[1<<i for i in range(7) for _ in range(2)]+[(1<<i)|(1<<j) for i in range(7) for j in range(i)]
 if sorted(support[u] for u in U)!=sorted(expected):raise ValueError('bad support multiplicities')
 if any(len(g[e])!=7 for e in E) or any(g[u]&set(U) for u in U):raise ValueError('not empty-complete')
 if any(len(g[e]&g[h])!=1 for e in E for h in H):raise ValueError('high-empty saturation')
 if any(len(g[u]&g[v])>1 for u in range(49) for v in range(u)):raise ValueError('C4')
 if any(7-len(g[u]) not in (4,5) for u in U):raise ValueError('residualdegree not4or5')
 return [sum(1<<v for v in ns) for ns in g],support,E,U

def complete_domains(g,support,U,budget):
 initial={}
 for u in U:
  existing=[v for v in range(49) if g[u]>>v&1]
  candidates=[v for v in U if v!=u and all(not g[v]&g[w] for w in existing)]
  buckets=[[v for v in candidates if support[v]>>h&1] for h in range(7)]
  rows=[]
  def visit(left,need,row,neighbour_union):
   budget.tick()
   if need==0:
    if left==0:rows.append(row)
    return
   if not need<=left.bit_count()<=2*need:return
   h=(left&-left).bit_length()-1
   for v in buckets[h]:
    if support[v]&~left or g[v]&neighbour_union:continue
    visit(left^support[v],need-1,row|(1<<v),neighbour_union|g[v])
  try:visit(127,7-g[u].bit_count(),0,0)
  except Limit:return {'status':'UNKNOWN','stage':'generation','vertex':u,'initial':initial,'nodes':budget.nodes}
  assert len(rows)==len(set(rows))
  initial[u]=rows
 return {'status':'DOMAINS_COMPLETE','initial':initial,'nodes':budget.nodes}

def arc_consistency(g,initial,budget):
 domains={u:list(rows) for u,rows in initial.items()};events=[];vertices=sorted(domains)
 for u in vertices:
  if not domains[u]:return {'status':'INFEASIBLE_ARC','initial':initial,'events':events,'empty_vertex':u,'nodes':budget.nodes}
 try:
  changed=True
  while changed:
   changed=False
   for u in vertices:
    for v in vertices:
     if u==v:continue
     removed=[]
     for a in domains[u]:
      supported=False
      for b in domains[v]:
       budget.tick()
       if ((a>>v)&1)==((b>>u)&1) and ((g[u]|a)&(g[v]|b)).bit_count()<=1:
        supported=True;break
      if not supported:removed.append(a)
     if removed:
      bad=set(removed);domains[u]=[a for a in domains[u] if a not in bad];events.append({'vertex':u,'against':v,'removed':removed});changed=True
      if not domains[u]:return {'status':'INFEASIBLE_ARC','initial':initial,'events':events,'empty_vertex':u,'nodes':budget.nodes}
 except Limit:return {'status':'UNKNOWN','stage':'arc','initial':initial,'events':events,'remaining':domains,'nodes':budget.nodes}
 return {'status':'ARC_FEASIBLE','initial':initial,'events':events,'remaining':domains,'nodes':budget.nodes}

def check(adjacency,*,max_nodes=100000,deadline=None):
 g,support,E,U=validate(adjacency);budget=Budget(max_nodes,deadline)
 result=complete_domains(g,support,U,budget)
 if result['status']=='UNKNOWN':return result
 for u,rows in result['initial'].items():
  if not rows:return {'status':'INFEASIBLE_ROW','initial':result['initial'],'empty_vertex':u,'nodes':budget.nodes}
 return arc_consistency(g,result['initial'],budget)
