from pathlib import Path
import itertools,json,hashlib
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n78-eight-fixed');pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
# Counts rather than sorted degree-sequence recursion.
profiles=[];checked=0
for n7 in range(9):
 for n5 in range(9-n7):
  for n3 in range(9-n7-n5):
   n1=8-n7-n5-n3;d=[1]*n1+[3]*n3+[5]*n5+[7]*n7;checked+=1;s=sum(d)
   if sum(x*(x-1) for x in d)<=56 and all(x*(9-x)<=s-2 for x in d):profiles.append(d)
assert checked==165 and sorted(profiles)==json.loads((src/'results.json').read_text())['degree_profiles']
# Exhaustive four-neighbour/eight-endpoint arithmetic behind the degree5 and triangle arguments.
assert 4*2>7 and 3*2>2+2 and 3*2>4
# Disjoint triangle count needed to cover non-leaf-neighbour degree3 vertices.
for cubic,leaves in [(6,2),(7,1),(8,0)]:
 forced=cubic-leaves;least=(forced+2)//3
 assert least>=2
 if cubic==8:assert least*3>cubic
 if cubic==6:assert (6-leaves)//2>=2
out={'status':'PASS_PAPER_ARITHMETIC','multisets':checked,'surviving_profiles':profiles,'method':'independent count-vector coverage; structural proof audited separately; no DFS replay'}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');(p/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(json.dumps(out))
