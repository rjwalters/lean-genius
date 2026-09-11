from pathlib import Path
from itertools import combinations_with_replacement,product
import json
p=Path(__file__).parent
patterns=[x for x in combinations_with_replacement(range(1,6),3) if sum(x)<=5]
assert patterns==[(1,1,1),(1,1,2),(1,1,3),(1,2,2)]
checks=0
for d in combinations_with_replacement(range(6),5):
 D=sum(d)
 for n1,n2,n3 in product(range(11),repeat=3):
  if n1+n2+n3>10 or D!=15-n1-2*n2-2*n3:continue
  C=n1+2*n2+3*n3
  e=45-2*C-sum(x*(x-1) for x in d)
  cross=70-2*e-(10+2*D)
  assert cross==30+2*sum(x*(x-4) for x in d)+4*n3
  assert cross==2*(sum((x-2)**2 for x in d)+2*n3-5)
  checks+=1
balanced=[]
for j,n1,n2,n3 in product(range(6),range(11),range(11),range(11)):
 if n1+n2+n3>10 or 10+j!=15-n1-2*n2-2*n3:continue
 cross=-10+2*j+4*n3
 assert cross==-2*n1-4*n2
 if cross>=0:balanced.append([j,10-n1-n2-n3,n1,n2,n3])
assert balanced==[[1,8,0,0,2],[3,9,0,0,1],[5,10,0,0,0]]
result={'status':'PASS','attached_patterns':patterns,'integer_identity_checks':checks,'balanced_numerical_cases_j_n111_n211_n221_n311':balanced,'scope':'Arithmetic identities and intermediate cases only; paper commutation/cardinality arguments exclude the first two balanced cases.'}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
