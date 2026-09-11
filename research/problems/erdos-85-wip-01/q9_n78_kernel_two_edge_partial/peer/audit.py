from pathlib import Path
import json,itertools as I,hashlib,sqlite3,time
p=Path(__file__).parent;b=Path('/Users/rwalters/lean-genius-q9-known-values-20260911');src=b/'n78-kernel-two-edge-partial';read=lambda f:json.loads(f.read_text());hashes={}
for mf in ['pins.json','input-pins.json']:
 for n,h in read(src/mf).items():
  f=src/n;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;hashes[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
states=[dict(con.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2257,2419,2425,2470,2472,2477]];assert all(s['status']=='resolved' and s['resolution'].startswith('PASS') for s in states)
old=next(r for r in read(b/'n78-kernel-two-dihedral-cover/results.json')['records'] if r['bits']==[1,1,1]);table=old['multiplication'];rot=4;t=table[rot][2];powers=[0]
for i in range(1,8):powers.append(table[powers[-1]][rot])
translation=[x for power in powers for x in [power,table[power][t]]];assert len(set(translation))==16;back={g:i for i,g in enumerate(translation)};M=[[back[table[x][y]] for y in translation] for x in translation];inv=[next(j for j in range(16) if M[i][j]==M[j][i]==0) for i in range(16)]
# Cosets computed from subgroup multiplication, independently of integer division.
cosets=sorted({tuple(sorted([g,M[g][1]])) for g in range(16)});coset={g:i for i,C in enumerate(cosets) for g in C};assert len(cosets)==8 and all(coset[g]==g//2 for g in range(16))
normalizer=[g for g in range(16) if M[g][1]==M[1][g]];assert normalizer==[0,1,8,9]
data=read(src/'results.json');assert data['status']=='COMPLETE';start=time.monotonic();status='INCOMPLETE';counts={'base':0,'W0':0,'W2':0,'positive':0};checked=[]
def graph(n,edges):
 A=[0]*n
 for u,v in edges:assert u!=v;A[u]|=1<<v;A[v]|=1<<u
 return A
def cycle(A,rec):
 C=rec['c4'];assert len(C)==len(set(C))==4 and all(0<=v<len(A) for v in C);assert all(A[C[i]]&(1<<C[(i+1)%4]) for i in range(4))
records={}
for r in data['records']:
 key=(r['u'],tuple(r['T']),r['stage'],r.get('d'),r.get('x'),tuple(r['D']) if 'D' in r else None);assert key not in records;records[key]=r
try:
 connections=[]
 for pair in I.combinations(range(1,16),2):
  if set(map(lambda x:inv[x],pair))!=set(pair):continue
  A=graph(16,[(g,M[g][h]) for g in range(16) for h in pair]);unseen=set(range(16));sizes=[]
  while unseen:
   component={min(unseen)}
   while True:
    expanded=component|{v for u in component for v in range(16) if A[u]&(1<<v)}
    if expanded==component:break
    component=expanded
   unseen-=component;sizes.append(len(component))
  if sorted(sizes)==[8,8]:connections.append(pair)
 assert connections==list(map(tuple,data['connections'])) and len(connections)==6
 triples=[(0,a,b) for a,b in I.combinations(range(1,16),2)];assert triples==list(map(tuple,data['triples']))
 for u in [0,1]:
  # Original characters 01 and10 become (r,t)=(0,1),(1,1).
  character=next(m for m in old['models'] if m['character']==([0,1] if u==0 else [1,0]))
  ds=[g for g in range(16) if character['S_action'][translation[g]][0]==1];assert len(ds)==8
  for T in connections:
   if time.monotonic()-start>30:raise TimeoutError
   bedges=[(8+g,8+M[g][h]) for g in range(16) for h in T]+[(coset[g],8+g) for g in range(16)]+[(coset[g],coset[M[g][8]]) for g in range(16)]
   counts['base']+=1;key=(u,T,'base',None,None,None)
   if key in records:cycle(graph(24,bedges),records.pop(key));checked.append(key);continue
   for d,x in I.product(ds,range(8)):
    wedges=bedges+[(24+g,v) for g in range(16) for v in [coset[M[g][cosets[x][0]]],8+g,8+M[g][d]]];counts['W0']+=1;key=(u,T,'W0',d,x,None)
    if key in records:cycle(graph(40,wedges),records.pop(key));checked.append(key);continue
    for D in triples:
     if time.monotonic()-start>30:raise TimeoutError
     all_edges=wedges+[(40+g,8+M[g][h]) for g in range(16) for h in D];key=(u,T,'W2',d,x,D);cycle(graph(56,all_edges),records.pop(key));checked.append(key);counts['W2']+=1
 assert not records and counts==data['counts']=={'base':12,'W0':512,'W2':8400,'positive':0}
 status='COMPLETE'
except TimeoutError:pass
out={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':hashes,'premises':states,'counts':counts,'checked_keys':checked};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':status,'seconds':out['seconds'],'hashes':len(hashes),'counts':counts,'certificates':len(checked)}))
