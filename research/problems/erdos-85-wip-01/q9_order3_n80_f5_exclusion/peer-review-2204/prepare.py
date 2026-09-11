from pathlib import Path
from itertools import permutations,product
import json,hashlib
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-row-supported-color-cover');d=Path(__file__).resolve().parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
pin=json.loads((s/'input-pin.json').read_text());inp=Path(pin['path']);assert hashlib.sha256(inp.read_bytes()).hexdigest()==pin['sha256']
rs=list(map(json.loads,(s/'receipts.jsonl').read_text().splitlines()));assert len(rs)==len({r['code'] for r in rs})==576
assert sum(r['status']=='COMPLETE_NEGATIVE' for r in rs)==516
unknown=[r['code'] for r in rs if r['status']=='UNKNOWN'];assert len(unknown)==60
assert all(r['nodes']==100000 and not r['words'] for r in rs if r['status']=='UNKNOWN')
(d/'unknown-not-replayed.json').write_text(json.dumps(unknown)+'\n')
lines=inp.read_text().splitlines()[1:];ps=list(permutations(range(3)));words=list(product(range(3),repeat=5));out=[]
for line,r in zip(lines,rs):
 data=list(map(int,line.split()));assert data[0]==r['code']
 if r['status']!='COMPLETE_NEGATIVE':continue
 z=data[0];ds=[]
 for i in range(10):ds.append(z%6);z//=6
 ds.reverse();P={};i=0
 for u in range(5):
  for v in range(u+1,5):
   perm=ps[ds[i]];i+=1;P[u,v]=perm;P[v,u]=tuple(perm.index(a) for a in range(3))
 B=[]
 for w in words:
  for u in range(5):
   arrivals=[P[v,u][w[v]] for v in range(5) if v!=u]
   if w[u]:arrivals.append(3-w[u])
   B.extend(3-arrivals.count(a) for a in range(3))
 out.append(line+' '+' '.join(map(str,B)))
assert len(out)==516
(d/'input.txt').write_text('516\n'+'\n'.join(out)+'\n')
print('Pins/input link verified; 516 completed cases prepared; 60 UNKNOWN omitted')
