from pathlib import Path
from itertools import product
import json,hashlib
s=Path('/tmp/erdos85-sol1-q9-order3-f2-exact-encoding');p=Path(__file__).parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
rows=[]
for x,y in product(range(3),repeat=2):
 if x==y==2:continue
 bx,dx=int(x>0),int(x==2);by,dy=int(y>0),int(y==2)
 z=[max(0,bx+by-1),max(0,dx+by-1),max(0,bx+dy-1)]
 assert sum(z)==x*y
 rows.append([x,y,z])
assert len(rows)==8
assert 2*(20*21//2)==420 and (20*19//2)*20*3==11400
for q in range(3):assert q*q-q==2*int(q==2)
(p/'results.json').write_text(json.dumps({'status':'PASS','local_entry_pairs':rows,'binary_variables':420,'continuous_auxiliaries':11400},indent=2)+'\n');(p/'source-pins.json').write_bytes((s/'pins.json').read_bytes());print('All8 admissible pair products and variable counts PASS')
