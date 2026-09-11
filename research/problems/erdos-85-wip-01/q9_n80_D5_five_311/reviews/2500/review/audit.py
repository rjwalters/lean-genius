from pathlib import Path
import json,hashlib,itertools as it,time,functools,sqlite3
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');out=Path(__file__).parent
names=['high-center-pairs','high-center-assignments','full-center-configurations'];nh=0
for name in names:
 base=b/('residual-ten-D5-five-311-'+name)
 for fn in ['pins.json','input-pins.json']:
  for k,v in json.loads((base/fn).read_text()).items():
   p=Path(k);p=p if p.is_absolute() else base/p
   assert hashlib.sha256(p.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2478,2488,2492,2495,2497]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
def data(name):return json.loads((b/('residual-ten-D5-five-311-'+name)/'results.json').read_text())
def records(name):return {r['root']:r for r in data(name)['records']}
dom=records('center-domains');prop=records('low-propagation');edgecases=records('low-edge-capacity');joint=records('nonempty-joint');graphs=records('high-matchings');cross=records('center-cross-domains');prior=records('center-cross-cover');pairs=records('high-center-pairs');assign=records('high-center-assignments');configs=records('full-center-configurations');required={k for k,v in prior.items() if v['witness'] is not None};assert pairs.keys()==assign.keys()==configs.keys()==required and len(required)==29
for name in names:assert data(name)['status']=='COMPLETE'
context={}
for root in required:
 d=dom[root];r=cross[root];src=d['source_root'];ai=d['source_assignment'];lows=next(x['lows'] for x in edgecases[src]['survivors'] if x['assignment']==ai);pr=next(x for x in prop[src]['survivors'] if x['assignment']==ai);j=joint[src];hg=graphs[j['packing_root']]['survivors'][j['graph']]['edges'];matched={v//2 for e in hg for v in e};F=[set() for _ in range(60)]
 for u,v in list(map(tuple,hg))+[(v,10+i) for i,(v,_) in enumerate(lows) if v>=0]+[(10+i,10+j) for i,j in pr['forced_edges']]:F[u].add(v);F[v].add(u)
 P=[set(x) for x in F]
 for u,v in pr['remaining_edges']:P[10+u].add(10+v);P[10+v].add(10+u)
 HV=[[{2*f,2*f+1}|{10+v for i in g for v in d['low_orbits'][i]} for g in gs] for f,gs in enumerate(r['high_groups'])];LV=[{10+v for i in g['orbits'] for v in d['low_orbits'][i]} for g in r['low_groups']];degrees=[[1+sum(lows[d['low_orbits'][i][0]][0]<0 for i in g)-int(f in matched) for g in gs] for f,gs in enumerate(r['high_groups'])];assert degrees==pairs[root]['degrees'];context[root]=(F,P,HV,LV)
def hall(A,B,P):
 if len(A)!=len(B):return False
 A=tuple(A)
 for mask in range(1,1<<len(A)):
  neighbors=set()
  for i,u in enumerate(A):
   if mask>>i&1:neighbors|=P[u]&B
  if len(neighbors)<mask.bit_count():return False
 return True
def domain(A,B,F,P,optional):
 if A&B:return 0
 edges={(u,v) for u in A for v in F[u]&B};bits=0 if edges else 2
 if len({u for u,v in edges})!=len(edges) or len({v for u,v in edges})!=len(edges):return bits
 A=A-{u for u,v in edges};B=B-{v for u,v in edges}
 if not optional:return bits|int(hall(A,B,P))
 # Select which optional high endpoints participate, then verify every Hall subset.
 AA={u for u in A if u>=10};BB={u for u in B if u>=10};ao=sorted(A-AA);bo=sorted(B-BB)
 for x in range(1<<len(ao)):
  L=AA|{v for i,v in enumerate(ao) if x>>i&1}
  for y in range(1<<len(bo)):
   R=BB|{v for i,v in enumerate(bo) if y>>i&1}
   if hall(L,R,P):return bits|1
 return bits
start=time.monotonic();status='INCOMPLETE';tested=neither=0
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
try:
 for root,r in pairs.items():
  F,P,HV,LV=context[root];lookup={tuple(e[:4]):e[4] for e in r['pair_domains']};assert len(lookup)==len(r['pair_domains']);expected={}
  for f,g in it.combinations(range(5),2):
   for i,A in enumerate(HV[f]):
    for j,B in enumerate(HV[g]):
     guard();bits=domain(A,B,F,P,True);expected[f,g,i,j]=bits;tested+=1;neither+=bits==0
  assert lookup==expected
 assert (tested,neither)==(24819,12782);status='COMPLETE'
except TimeoutError:pass
s1=dict(status=status,seconds=time.monotonic()-start,original_cap_seconds=30,pairs=tested,neither=neither);(out/'stage1.json').write_text(json.dumps(s1,indent=2)+'\n');print(s1,flush=True);assert status=='COMPLETE'
start=time.monotonic();status='INCOMPLETE';before=after=positive=0
try:
 for root,r in pairs.items():
  guard();c=cross[root];lo=c['low_groups'];lm=[sum(1<<v for v in g['orbits']) for g in lo];hm=[[sum(1<<v for v in g) for g in gs] for gs in c['high_groups']];compat=[[set(xs) for xs in ds] for ds in c['compatibility']];lookup={tuple(e[:4]):e[4] for e in r['pair_domains']};found={};tested=0
  for E in it.combinations(list(it.combinations(range(5),2)),2):
   degree=[sum(v in e for e in E) for v in range(5)];opts=[[j for j,d in enumerate(ds) if d==degree[f]] for f,ds in enumerate(r['degrees'])]
   def visit(selected,used,allowed):
    global tested
    guard();f=len(selected)
    if f==5:
     tested+=1;rem=((1<<25)-1)^used;ids=sorted(i for i in allowed if lm[i]&rem==lm[i]);z=sum(lo[i]['inactive']>0 for i in ids);union=0
     for i in ids:union|=lm[i]
     if len(ids)>=5 and z>=1 and len(ids)-z>=4 and union==rem:found[(E,selected)]=(rem,ids)
     return
    for j in opts[f]:
     m=hm[f][j]
     if m&used:continue
     if any(not lookup[g,f,k,j]&(2 if (g,f) in E else 1) for g,k in enumerate(selected)):continue
     a=allowed&compat[f][j]
     if len(a)>=5:visit(selected+(j,),used|m,a)
   visit((),0,set(range(len(lo))))
  saved=assign[root];assert saved['status']=='COMPLETE' and tested==saved['complete_assignments'];actual={(tuple(map(tuple,h['high_edges'])),tuple(h['high_options'])):(h['remaining'],h['low_options']) for h in saved['survivors']};assert len(actual)==len(saved['survivors']) and actual==found;before+=tested;after+=len(found);positive+=bool(found)
 assert (before,after,positive)==(139,136,21);status='COMPLETE'
except TimeoutError:pass
s2=dict(status=status,seconds=time.monotonic()-start,original_cap_seconds=30,before_filter=before,assignments=after,positive_cases=positive);(out/'stage2.json').write_text(json.dumps(s2,indent=2)+'\n');print(s2,flush=True);assert status=='COMPLETE'
# Enumerate all low partitions using the smallest uncovered orbit. Canonicalize
# Y-center labels by sorted low-option index to compare independent traversal.
def canonical(selected,E):
 ordered=sorted(selected);mapping={5+j:5+ordered.index(li) for j,li in enumerate(selected)}
 def relabel(v):return v if v<5 else mapping[v]
 return (tuple(ordered),tuple(sorted(tuple(sorted((relabel(u),relabel(v)))) for u,v in E)))
start=time.monotonic();status='INCOMPLETE';total=casecount=highcount=0
try:
 for root,saved in configs.items():
  guard();assert saved['status']=='COMPLETE';source=assign[root];c=cross[root];lo=c['low_groups'];lm=[sum(1<<v for v in g['orbits']) for g in lo];F,P,HV,LV=context[root];byrec={r['high_assignment']:r for r in saved['configs']};assert len(byrec)==len(saved['configs'])==len(source['survivors']);ncase=0
  @functools.lru_cache(None)
  def lowpair(i,j):return domain(LV[i],LV[j],F,P,False)
  for hi,h in enumerate(source['survivors']):
   guard();rec=byrec[hi];assert rec['status']=='COMPLETE';XX=list(map(tuple,h['high_edges']));goals=[3-sum(v in e for e in XX) for v in range(5)];by=[tuple(i for i in h['low_options'] if lm[i]>>v&1) for v in range(25)];found=set()
   def partition(rem,selected,z,degrees):
    guard()
    if not rem:
     if z!=1 or list(degrees)!=goals:return
     patterns=[lo[i]['active'] for i in selected];XY=[(v,5+j) for j,A in enumerate(patterns) for v in range(5) if not A>>v&1];ys=[j for j,A in enumerate(patterns) if A.bit_count()==3];assert len(ys)==4
     for mate in ys[1:]:
      rest=[v for v in ys[1:] if v!=mate];YY={tuple(sorted((ys[0],mate))),tuple(rest)}
      if any(not lowpair(*sorted((selected[i],selected[j])))&(2 if (i,j) in YY else 1) for i,j in it.combinations(range(5),2)):continue
      E=XX+XY+[(5+i,5+j) for i,j in YY];N=[set() for _ in range(10)]
      for u,v in E:N[u].add(v);N[v].add(u)
      assert all(len(x)==3 for x in N)
      if all(len(a&b)<=1 for a,b in it.combinations(N,2)):found.add(canonical(selected,E))
     return
    v=(rem&-rem).bit_length()-1
    for i in by[v]:
     m=lm[i];x=lo[i]
     if m&rem!=m or z+x['inactive']>1:continue
     if any(((31^x['active'])&(31^lo[j]['active'])).bit_count()>1 for j in selected):continue
     ds=tuple(d+int(not x['active']>>v&1) for v,d in enumerate(degrees))
     if any(d>goal for d,goal in zip(ds,goals)):continue
     if any(not lowpair(*sorted((i,j))) for j in selected):continue
     partition(rem^m,selected+(i,),z+x['inactive'],ds)
   partition(h['remaining'],(),0,(0,)*5)
   expected={canonical(r['low_options'],r['center_edges']) for r in rec['survivors']};assert len(expected)==len(rec['survivors']) and expected==found
   total+=len(found);ncase+=len(found);highcount+=1
  casecount+=bool(ncase)
 assert (total,casecount,highcount)==(706,13,136);status='COMPLETE'
except TimeoutError:pass
s3=dict(status=status,seconds=time.monotonic()-start,original_cap_seconds=30,configurations=total,positive_cases=casecount,high_assignments=highcount);(out/'stage3.json').write_text(json.dumps(s3,indent=2)+'\n');(out/'audit.json').write_text(json.dumps(dict(hashes=nh,stages=[s1,s2,s3]),indent=2)+'\n');print(s3,flush=True);assert status=='COMPLETE'
