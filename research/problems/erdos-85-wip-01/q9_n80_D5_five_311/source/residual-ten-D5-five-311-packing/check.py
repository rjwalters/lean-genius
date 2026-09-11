from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;start=time.monotonic();data=json.loads((p.parent/'residual-ten-D5-supports/results.json').read_text());out=[]
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 for c in data['records']:
  guard();R=[set() for _ in range(10)]
  for a,b in c['edges']:R[a].add(b);R[b].add(a)
  ds=list(map(len,R));supports=[[set(s),{v^1 for v in s}] for s in c['high3']];pairs={tuple(x) for x in c['compatible_pairs']['33']};adj=[{j for j in range(i+1,len(supports)) if (i,j) in pairs} for i in range(len(supports))]
  rec={'class':c['class'],'status':'UNKNOWN','compatible_packings':0,'q_nonnegative':0,'comm_pass':0,'survivors':[]};out.append(rec)
  def cliques(chosen,candidates):
   guard()
   if len(chosen)==5:yield chosen;return
   if len(chosen)+len(candidates)<5:return
   for i in sorted(candidates):yield from cliques(chosen+[i],candidates&adj[i])
  for selected in cliques([],set(range(len(supports)))):
   rec['compatible_packings']+=1;S=[s for i in selected for s in supports[i]];low=[9-ds[e]-sum(e in s for s in S) for e in range(10)]
   if min(low)<0:continue
   Z=[[int(i!=j and not R[i]&R[j] and not any(i in s and j in s for s in S)) for j in range(10)] for i in range(10)]
   q=[6-ds[i]-sum(Z[i]) for i in range(10)]
   if min(q)<0:continue
   rec['q_nonnegative']+=1
   D=[[sum(Z[k][j] for k in R[i])-sum(Z[i][k] for k in R[j]) for j in range(10)] for i in range(10)]
   if any(not -q[j]<=D[i][j]<=q[i] for i in range(10) for j in range(10)):continue
   rec['comm_pass']+=1;rec['survivors'].append({'high3':selected,'q':q})
  rec['status']='COMPLETE'
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
covered={r['class'] for r in out}
for c in data['records']:
 if c['class'] not in covered:out.append({'class':c['class'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'counts':[{k:v for k,v in r.items() if k!='survivors'} for r in out]}))
