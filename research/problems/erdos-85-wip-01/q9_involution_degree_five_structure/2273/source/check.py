import itertools,json,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'q9-involution-n80-degree-five-centers'

def run():
 start=time.monotonic();total=0;results=[]
 cases=json.loads((BASE/'results.json').read_text())['retained']
 graphs=json.loads((BASE/'representatives.json').read_text())
 for t,case in itertools.product(range(2),cases):
  H=[set() for _ in range(10)]
  for a,b in graphs[case['graph_index']]['edges']:H[a].add(b);H[b].add(a)
  P=set(case['P']);targets=[6]+[3 if t and j in (1,2) else 2 for j in range(1,5)]
  Q=[[int(i==0 or j==0 or (t and {i,j}=={1,2})) for j in range(5)] for i in range(5)]
  domains=[]
  for f in range(10):
   rows=[]
   for mask in range(32):
    y=tuple((mask>>j)&1 for j in range(5));delta=2-sum(y)
    if delta<0 or y[0]!=int(f not in P) or case['degree_P'][f]>1+delta:continue
    b=tuple(sum(y[k]*Q[k][j] for k in range(5))+delta for j in range(5))
    rows.append((y,b))
   domains.append(rows)
  nodes=0;assigned={};cols=[0]*5;witness=None
  def dfs():
   nonlocal nodes,total,witness
   if time.monotonic()-start>=30 or total>=500000 or nodes>=100000:raise TimeoutError
   nodes+=1;total+=1
   if len(assigned)==10:
    if cols==targets:witness=[list(assigned[f][0]) for f in range(10)];return True
    return False
   viable={}
   for f in range(10):
    if f in assigned:continue
    allowed=[]
    for y,b in domains[f]:
     if any(cols[j]+y[j]>targets[j] for j in range(5)):continue
     if any(sum(assigned[g][0][j] for g in H[f] if g in assigned)>b[j] for j in range(5)):continue
     if any(sum(assigned[h][0][j] for h in H[g] if h in assigned)+y[j]>assigned[g][1][j] for g in H[f] if g in assigned for j in range(5)):continue
     allowed.append((y,b))
    if not allowed:return False
    viable[f]=allowed
   if any(cols[j]+sum(min(row[0][j] for row in rows) for rows in viable.values())>targets[j] or cols[j]+sum(max(row[0][j] for row in rows) for rows in viable.values())<targets[j] for j in range(5)):return False
   f=min(viable,key=lambda f:(len(viable[f]),-len(H[f]&assigned.keys()),f))
   for y,b in viable[f]:
    assigned[f]=(y,b)
    for j in range(5):cols[j]+=y[j]
    if dfs():return True
    for j in range(5):cols[j]-=y[j]
    del assigned[f]
   return False
  if time.monotonic()-start>=30 or total>=500000:status='UNVISITED'
  else:
   try:status='WITNESS' if dfs() else 'INFEASIBLE'
   except TimeoutError:status='UNKNOWN'
  results.append(dict(t=t,case=case,status=status,nodes=nodes,witness=witness))
  (ROOT/'results.json').write_text(json.dumps(dict(elapsed=time.monotonic()-start,total_nodes=total,results=results),indent=2)+'\n')
 return dict(elapsed=time.monotonic()-start,total_nodes=total,counts={s:sum(r['status']==s for r in results) for s in ['WITNESS','INFEASIBLE','UNKNOWN','UNVISITED']})
if __name__=='__main__':print(json.dumps(run()))
