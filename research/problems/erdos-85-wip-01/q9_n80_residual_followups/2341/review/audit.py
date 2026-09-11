from pathlib import Path
import json,itertools as it,hashlib,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/residual-ten-11123-full-311')
for manifest in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/manifest).read_text()).items():
  f=Path(n) if Path(n).is_absolute() else src/n
  assert hashlib.sha256(f.read_bytes()).hexdigest()==h
rs=json.loads((src.parent/'residual-ten-11123-supports/results.json').read_text())['records'];saved=json.loads((src/'results.json').read_text());start=time.monotonic()
def allmatch(vs):
 if not vs:yield ();return
 a,*rest=vs
 for m in allmatch(rest):yield m
 for b in rest:
  for m in allmatch([v for v in rest if v!=b]):yield ((a,b),)+m
ms=[]
for edges in allmatch(list(range(6))):
 E={tuple(sorted(e)) for e in edges}
 if E!={tuple(sorted((a^1,b^1))) for a,b in E}:continue
 if any(sum(v in e for e in E)!=1 for v in range(2,6)):continue
 ms.append(tuple(sorted(E)))
assert len(ms)==10
actual=[];witnesses={}
for gi,r in enumerate(rs):
 assert time.monotonic()-start<30,'UNKNOWN original30s'
 R=[set() for _ in range(10)]
 for a,b in r['edges']:R[a].add(b);R[b].add(a)
 got=set()
 for si,s in enumerate(r['supports']):
  remaining=[i for i in range(5) if i not in {v//2 for v in s}]
  supp=[s,sorted(v^1 for v in s)]+[[2*i+b] for i in remaining for b in range(2)]
  for E in ms:
   A=[a.copy() for a in R]+[set() for _ in range(7)]
   def edge(a,b):A[a].add(b);A[b].add(a)
   for i,T in enumerate(supp):
    edge(10+i,16)
    for v in T:edge(10+i,v)
   for a,b in E:edge(a+10,b+10)
   valid=True;seen=set()
   for row in A:
    for pair in it.combinations(sorted(row),2):
     if pair in seen:valid=False;break
     seen.add(pair)
    if not valid:break
   if not valid:continue
   for i,T in enumerate(supp):
    excess=sum(len(R[v])-1 for v in T)
    for j in A[10+i]:
     if 10<=j<16:excess+=len(supp[j-10])-1
    if excess>2:valid=False;break
   if valid:got.add((si,E));witnesses[(gi,si,E)]=[sorted(a) for a in A]
 expected={(c['support_index'],tuple(sorted(tuple(sorted(e)) for e in c['internal_matching']))) for c in saved['records'][gi]['configurations']}
 assert got==expected;actual.append(len(got))
for w in json.loads((src/'witnesses.json').read_text()):
 c=w['configuration'];E=tuple(sorted(tuple(sorted(e)) for e in c['internal_matching']));assert witnesses[(w['input_graph'],c['support_index'],E)]==w['adjacency']
res=dict(status='COMPLETE',cap_seconds=30,seconds=time.monotonic()-start,matchings=len(ms),graphs=len(actual),positive_graphs=sum(bool(n) for n in actual),configurations=sum(actual),witnesses=4)
p.joinpath('audit.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res))
