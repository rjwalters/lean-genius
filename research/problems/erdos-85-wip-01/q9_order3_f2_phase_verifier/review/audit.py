from pathlib import Path
from itertools import combinations
import importlib.util,json,hashlib,time,subprocess,sys
src=Path('/tmp/erdos85-sol1-q9-order3-f2-phase-verifier');out=Path(__file__).parent;start=time.monotonic()
def read(p):return json.loads(p.read_text())
pins=read(src/'pins.json')
for n,h in pins.items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==h,n
inputs=read(src/'input-pins.json')
for n,h in inputs.items():assert hashlib.sha256(Path(n).read_bytes()).hexdigest()==h,n
path=Path('/tmp/erdos85-sol1-q9-order3-f2-neighbor-matching/inputs.txt');raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()=='ba3f8cbb932d278020ff6510a877099ec63ea5833a298c9f59a1025841cf54e6'
records=[list(map(int,line.split())) for line in raw.splitlines()];selected=[0]
for predicate in [lambda r:any(r[19+2*j:21+2*j]==[-1,-1] for j in range(20)),lambda r:sum(v<0 for v in r[19:])==2 and not any(r[19+2*j:21+2*j]==[-1,-1] for j in range(20))]:
 selected.append(next(i for i,r in enumerate(records) if predicate(r)))
spec=importlib.util.spec_from_file_location('candidate_verifier',src/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
def reverse(m):return sum(1<<((-t)%3) for t in range(3) if m&(1<<t))
fixtures=[]
for phase in selected:
 for kind in ['zero','degree_seven','dense','mixed']:
  D=[[0]*20 for _ in range(20)]
  for i in range(20):
   D[i][i]=6 if kind=='dense' or (kind=='mixed' and i%3==0) else 0
   for j in range(i+1,20):
    m=0 if kind=='zero' else (int((j-i)%20 in [1,2,3,10,17,18,19]) if kind=='degree_seven' else (7 if kind=='dense' else ((i+1)*101+(j+1)*37+phase)%8))
    D[i][j]=m;D[j][i]=reverse(m)
  fixtures.append({'phase_index':phase,'kind':kind,'D':D})
entries=degrees_checked=0;details=[]
for f in fixtures:
 assert time.monotonic()-start<60
 rec=records[f['phase_index']];D=f['D'];adj=[set() for _ in range(80)]
 def edge(a,b):adj[a].add(b);adj[b].add(a)
 for a in range(18):
  edge(a//9,2+a)
  for b in range(a+1,18):
   if rec[1+a]&(1<<b):edge(2+a,2+b)
 for i in range(20):
  for g in range(3):
   for side in range(2):
    endpoint=rec[19+2*i+side]
    if endpoint>=0:edge(20+3*i+g,2+9*side+3*(endpoint//3)+(endpoint%3+g)%3)
 for i in range(20):
  for j in range(20):
   for t in range(3):
    if D[i][j]&(1<<t):
     for g in range(3):edge(20+3*i+g,20+3*j+(g+t)%3)
 assert all(i not in adj[i] for i in range(80))
 ar,rr,ds=v.counts(rec,D)
 for g in range(3):
  for a in range(6):
   for i in range(20):
    for t in range(3):assert ar[a][i][t]==len(adj[2+3*a+g]&adj[20+3*i+(g+t)%3]);entries+=1
  for i in range(20):
   assert ds[i]==len(adj[20+3*i+g]);degrees_checked+=1
   for j in range(20):
    for t in range(3):assert rr[i][j][t]==len(adj[20+3*i+g]&adj[20+3*j+(g+t)%3]);entries+=1
 exact=all(len(a)==9 for a in adj) and all(len(adj[i]&adj[j])<=1 for i,j in combinations(range(80),2))
 result=v.verify(rec,D);assert result['valid']==exact
 assert all(len(adj[i])==9 for i in range(20))
 if f['phase_index']==0 and f['kind']=='degree_seven':assert ds==[9]*20 and not exact
 details.append({'phase':f['phase_index'],'kind':f['kind'],'valid':exact,'all_residual_degrees_nine':ds==[9]*20})
# Malformed candidates fail before counting; booleans are not integer masks.
base=[[0]*20 for _ in range(20)];bad=[]
bad.append(base[:-1]);bad.append([[False]*20 for _ in range(20)]);bad.append([[0.0]*20 for _ in range(20)])
for i,j,value in [(0,0,1),(0,1,2),(0,0,8),(0,0,-1)]:
 z=[r.copy() for r in base];z[i][j]=value;bad.append(z)
for D in bad:
 try:v.counts(records[0],D)
 except AssertionError:pass
 else:raise AssertionError('malformed candidate accepted')
(out/'fixtures.json').write_text(json.dumps(fixtures)+'\n')
(out/'cli-zero.json').write_text(json.dumps({'phase_index':0,'D':base})+'\n')
r=subprocess.run([sys.executable,str(src/'verify.py'),str(out/'cli-zero.json'),str(path)],capture_output=True,text=True);assert r.returncode==1 and json.loads(r.stdout)['valid'] is False
(out/'wrong-input.txt').write_text('0\n')
r=subprocess.run([sys.executable,str(src/'verify.py'),str(out/'cli-zero.json'),str(out/'wrong-input.txt')],capture_output=True,text=True);assert r.returncode!=0 and 'AssertionError' in r.stderr
result={'status':'PASS','fixtures':len(fixtures),'phases':selected,'exact_block_entries':entries,'degree_checks':degrees_checked,'malformed_cases':len(bad),'cli_checks':2,'seconds':time.monotonic()-start,'details':details,'graph_search_calls':0}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
(out/'input-pins.json').write_text(json.dumps({str(src/'pins.json'):hashlib.sha256((src/'pins.json').read_bytes()).hexdigest(),**inputs},indent=2)+'\n')
