from pathlib import Path
import json,time,itertools as it,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-center-cross-domains/results.json').read_text())['records'];out=[];edgecases={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records']};joint={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records']};graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};prior={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-cross-cover/results.json').read_text())['records']};original={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-domains/results.json').read_text())['records']};prop={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records']}
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
try:
 for r in data:
  if prior[r['root']]['witness'] is None:continue
  guard();low=[(sum(1<<v for v in x['orbits']),x['active'],x['inactive']) for x in r['low_groups']];high=[[(sum(1<<v for v in g),sum(1<<li for li in r['compatibility'][i][j])) for j,g in enumerate(ds)] for i,ds in enumerate(r['high_groups'])];by=[[i for i,x in enumerate(low) if x[0]>>v&1] for v in range(25)];rec={'root':r['root'],'status':'UNKNOWN'};out.append(rec)
  orig=original[r['root']];lows=next(a['lows'] for a in edgecases[orig['source_root']]['survivors'] if a['assignment']==orig['source_assignment']);source=joint[orig['source_root']];Hg=graphs[source['packing_root']]['survivors'][source['graph']]['edges'];matched={v//2 for e in Hg for v in e};group_goals=[[2-sum(lows[orig['low_orbits'][oi][0]][0]<0 for oi in g)+int(f in matched) for g in ds] for f,ds in enumerate(r['high_groups'])];pa=next(a for a in prop[orig['source_root']]['survivors'] if a['assignment']==orig['source_assignment']);forced=[set() for _ in range(50)]
  for v,w in pa['forced_edges']:forced[v].add(w);forced[w].add(v)
  possible=[set(x) for x in forced]
  for v,w in pa['remaining_edges']:possible[v].add(w);possible[w].add(v)
  vertices=[set(v for oi in g['orbits'] for v in orig['low_orbits'][oi]) for g in r['low_groups']]
  @functools.lru_cache(None)
  def pairbits(i,j):
   guard();A=vertices[i];B=vertices[j]
   if A&B:return 0
   cross=[(v,w) for v in A for w in forced[v]&B];bits=0 if cross else 2;usedA={v for v,w in cross};usedB={w for v,w in cross}
   if len(usedA)!=len(cross) or len(usedB)!=len(cross):return bits
   left=sorted(A-usedA);right=sorted(B-usedB)
   @functools.lru_cache(None)
   def match(k,used):
    if k==len(left):return True
    return any(not used>>q&1 and w in possible[left[k]] and match(k+1,used|1<<q) for q,w in enumerate(right))
   if match(0,0):bits|=1
   return bits
  @functools.lru_cache(None)
  def center_graph(selected,goals):
   patterns=tuple(low[i][1] for i in selected);cross=[(v,5+j) for j,A in enumerate(patterns) for v in range(5) if not A>>v&1];d=[sum(v in e for e in cross) for v in range(5)];ones=[j for j,A in enumerate(patterns) if A.bit_count()==3]
   if len(ones)!=4 or tuple(d)!=goals:return None
   matchings=[[(ones[0],ones[1]),(ones[2],ones[3])],[(ones[0],ones[2]),(ones[1],ones[3])],[(ones[0],ones[3]),(ones[1],ones[2])]]
   for lm in matchings:
    lm={tuple(sorted(e)) for e in lm}
    if any(not pairbits(*sorted((selected[i],selected[j])))&(2 if (i,j) in lm else 1) for i,j in it.combinations(range(5),2)):continue
    for high in it.combinations(list(it.combinations(range(5),2)),2):
     if any(d[v]+sum(v in e for e in high)!=3 for v in range(5)):continue
     E=cross+list(high)+[(5+i,5+j) for i,j in lm];N=[set() for _ in range(10)]
     for v,w in E:N[v].add(w);N[w].add(v)
     if all(len(x&y)<=1 for x,y in it.combinations(N,2)):return E
   return None
  @functools.lru_cache(None)
  def lowcover(rem,selected,z,allowed,goals):
   patterns=tuple(low[i][1] for i in selected)
   guard()
   if not rem:
    if z!=1:return None
    graph=center_graph(selected,goals)
    return ((),graph) if graph is not None else None
   choices=min(([i for i in by[v] if allowed>>i&1 and low[i][0]&rem==low[i][0] and z+low[i][2]<=1 and all(((31^low[i][1])&(31^A)).bit_count()<=1 for A in patterns)] for v in range(25) if rem>>v&1),key=len)
   for li in choices:
    m,A,dz=low[li];newpatterns=patterns+(A,)
    if any(not pairbits(*sorted((li,j))) or ((dz or low[j][2]) and not pairbits(*sorted((li,j)))&1) for j in selected):continue
    allchosen=selected+(li,)
    if any(sum(not pairbits(*sorted((i,j)))&1 for j in allchosen if j!=i)>1 for i in allchosen):continue
    if any(sum(not X>>v&1 for X in newpatterns)>goals[v] for v in range(5)):continue
    tail=lowcover(rem^m,selected+(li,),z+dz,allowed,goals)
    if tail is not None:return ((li,)+tail[0],tail[1])
   return None
  @functools.lru_cache(None)
  def cover(pending,used,allowed,goals):
   guard()
   if allowed.bit_count()<5:return None
   if not pending:
    tail=lowcover(((1<<25)-1)^used,(),0,allowed,goals)
    return ((),tail) if tail is not None else None
   choices=[(i,[(j,m,allowed&ok) for j,(m,ok) in enumerate(high[i]) if not m&used and (allowed&ok).bit_count()>=5 and 1<=group_goals[i][j]<=3]) for i in range(5) if pending>>i&1];i,ds=min(choices,key=lambda x:len(x[1]))
   for j,m,newallowed in ds:
    newgoals=list(goals);newgoals[i]=group_goals[i][j]
    tail=cover(pending^(1<<i),used|m,newallowed,tuple(newgoals))
    if tail is not None:return (((i,j),)+tail[0],tail[1])
   return None
  witness=cover(31,0,(1<<len(low))-1,(-1,)*5);rec.update(status='COMPLETE',high_states=cover.cache_info().currsize,low_states=lowcover.cache_info().currsize,pair_states=pairbits.cache_info().currsize,witness=witness)
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
seen={r['root'] for r in out}
for r in data:
 if prior[r['root']]['witness'] is not None and r['root'] not in seen:out.append({'root':r['root'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'complete':sum(x['status']=='COMPLETE' for x in out),'negative':sum(x['status']=='COMPLETE' and x['witness'] is None for x in out),'positive':sum(x['status']=='COMPLETE' and x['witness'] is not None for x in out)}))
