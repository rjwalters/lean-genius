from pathlib import Path
import itertools as it,json,hashlib,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-normal-three-quotients')
for manifest in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/manifest).read_text()).items():
  f=Path(n) if Path(n).is_absolute() else src/n;assert hashlib.sha256(f.read_bytes()).hexdigest()==h
allcases=json.loads((src/'results.json').read_text())['cases'];cases=allcases[:2];assert all(c['status']=='COMPLETE' for c in cases);assert allcases[2]['status']=='UNKNOWN'
start=time.monotonic();reports=[]
def guard():
 if time.monotonic()-start>30:raise TimeoutError
def compositions(total,k):
 if k==1:yield(total,);return
 for x in range(total+1):
  for tail in compositions(total-x,k-1):yield(x,)+tail
try:
 for rec in cases:
  ns=rec['sizes'];N=7;pairs=list(it.combinations(range(N),2));cap=tuple(n*(n-1)//2 for n in ns)+tuple(ns[a]*ns[b] for a,b in pairs);options=[]
  for i in range(N):
   guard();opts={}
   for row in compositions(9,N):
    if row[i]>=ns[i] or ns[i]*row[i]%2:continue
    if any(ns[i]*row[j]%ns[j] or ns[i]*row[j]//ns[j]>9 for j in range(N) if j!=i):continue
    contribution=tuple(ns[i]*q*(q-1)//2 for q in row)+tuple(ns[i]*row[a]*row[b] for a,b in pairs)
    if any(a>b for a,b in zip(contribution,cap)):continue
    opts.setdefault(row[:i],[]).append((row,contribution))
   options.append(opts)
  found=set();nodes=[0]
  def walk(rows,remaining):
   guard();nodes[0]+=1;i=len(rows)
   if i==N:found.add(tuple(rows));return
   prefix=tuple(ns[j]*rows[j][i]//ns[i] for j in range(i))
   for row,cost in options[i].get(prefix,[]):
    rem=tuple(a-b for a,b in zip(remaining,cost))
    if min(rem)>=0:walk(rows+[row],rem)
  walk([],cap)
  expected={tuple(map(tuple,q)) for q in rec['quotients']};assert found==expected
  reports.append(dict(sizes=ns,quotients=len(found),nodes=nodes[0]))
 status='COMPLETE'
except TimeoutError:status='UNKNOWN'
r=dict(status=status,cap_seconds=30,seconds=time.monotonic()-start,review_scope='first two COMPLETE cases only',reports=reports,third_case_status='UNKNOWN unchanged; not enumerated')
p.joinpath('audit.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
