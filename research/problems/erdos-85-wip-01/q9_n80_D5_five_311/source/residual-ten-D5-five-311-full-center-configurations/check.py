from pathlib import Path
import json,itertools as it,time,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-high-center-assignments/results.json').read_text())['records'];cross={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-cross-domains/results.json').read_text())['records']};original={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-domains/results.json').read_text())['records']};prop={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records']};out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
try:
 for source in data:
  guard();c=cross[source['root']];o=original[source['root']];a=next(a for a in prop[o['source_root']]['survivors'] if a['assignment']==o['source_assignment']);forced=[set() for _ in range(50)]
  for v,w in a['forced_edges']:forced[v].add(w);forced[w].add(v)
  possible=[set(x) for x in forced]
  for v,w in a['remaining_edges']:possible[v].add(w);possible[w].add(v)
  low=[(sum(1<<i for i in g['orbits']),g['active'],g['inactive']) for g in c['low_groups']];vertices=[set(v for oi in g['orbits'] for v in o['low_orbits'][oi]) for g in c['low_groups']];rec={'root':source['root'],'status':'UNKNOWN','configs':[]};out.append(rec)
  @functools.lru_cache(None)
  def pairbits(i,j):
   guard();A=vertices[i];B=vertices[j]
   if A&B:return 0
   edges=[(v,w) for v in A for w in forced[v]&B];bits=0 if edges else 2;usedA={v for v,w in edges};usedB={w for v,w in edges}
   if len(usedA)!=len(edges) or len(usedB)!=len(edges):return bits
   left=sorted(A-usedA);right=sorted(B-usedB)
   @functools.lru_cache(None)
   def match(k,used):
    if k==len(left):return True
    return any(not used>>j&1 and w in possible[left[k]] and match(k+1,used|1<<j) for j,w in enumerate(right))
   if match(0,0):bits|=1
   return bits
  for hi,h in enumerate(source['survivors']):
   guard();E=list(map(tuple,h['high_edges']));goals=[3-sum(v in e for e in E) for v in range(5)];ids=h['low_options'];by=[[i for i in ids if low[i][0]>>v&1] for v in range(25)];record={'high_assignment':hi,'status':'UNKNOWN','survivors':[]};rec['configs'].append(record)
   def covers(rem,selected,z,degree):
    guard()
    if not rem:
     if z!=1 or degree!=goals:return
     patterns=[low[i][1] for i in selected];crossE=[(v,5+j) for j,A in enumerate(patterns) for v in range(5) if not A>>v&1];ones=[j for j,A in enumerate(patterns) if A.bit_count()==3];assert len(ones)==4
     matchings=[[(ones[0],ones[1]),(ones[2],ones[3])],[(ones[0],ones[2]),(ones[1],ones[3])],[(ones[0],ones[3]),(ones[1],ones[2])]]
     for lm in matchings:
      lm=set(tuple(sorted(e)) for e in lm)
      if any(not pairbits(*sorted((selected[i],selected[j])))&(2 if (i,j) in lm else 1) for i,j in it.combinations(range(5),2)):continue
      edges=E+crossE+[(5+i,5+j) for i,j in lm];N=[set() for _ in range(10)]
      for v,w in edges:N[v].add(w);N[w].add(v)
      if all(len(x&y)<=1 for x,y in it.combinations(N,2)):record['survivors'].append({'low_options':selected,'center_edges':edges})
     return
    choices=min(([i for i in by[v] if low[i][0]&rem==low[i][0] and z+low[i][2]<=1 and all(((31^low[i][1])&(31^low[j][1])).bit_count()<=1 for j in selected)] for v in range(25) if rem>>v&1),key=len)
    for i in choices:
     mask,A,dz=low[i];newdegree=[d+int(not A>>v&1) for v,d in enumerate(degree)]
     if any(d>goal for d,goal in zip(newdegree,goals)):continue
     if any(not pairbits(*sorted((i,j))) or ((dz or low[j][2]) and not pairbits(*sorted((i,j)))&1) for j in selected):continue
     allchosen=selected+[i]
     if any(sum(not pairbits(*sorted((v,w)))&1 for w in allchosen if w!=v)>1 for v in allchosen):continue
     covers(rem^mask,allchosen,z+dz,newdegree)
   covers(h['remaining'],[],0,[0]*5);record['status']='COMPLETE'
  rec['status']='COMPLETE'
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
seen={r['root'] for r in out}
for source in data:
 if source['root'] not in seen:out.append({'root':source['root'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'complete_cases':sum(r['status']=='COMPLETE' for r in out),'complete_high_configs':sum(c['status']=='COMPLETE' for r in out for c in r.get('configs',[])),'center_configurations':sum(len(c['survivors']) for r in out for c in r.get('configs',[])),'positive_cases':sum(any(c['survivors'] for c in r.get('configs',[])) for r in out)}))
