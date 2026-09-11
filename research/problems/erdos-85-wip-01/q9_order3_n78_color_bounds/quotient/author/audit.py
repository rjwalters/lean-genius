from itertools import product
from pathlib import Path
import json
rows=[b for b in product(range(4),repeat=3) if sum(b)==6]
valid=[b for b in rows if sum(max(0,3*x-s) for x,s in zip(b,(6,5,5)))<=3]
assert valid==[(2,2,2)]
# Local row arithmetic: multiplicities0/1/2, sum6 and norm<=8 imply <=one2 and >=five positive entries.
profiles=[]
for doubles in range(4):
 singles=6-2*doubles
 if singles<0:continue
 norm=4*doubles+singles
 if norm<=8:
  assert doubles<=1 and doubles+singles>=5
  profiles.append({'singles':singles,'doubles':doubles,'norm':norm})
result={'status':'PASS_SMALL_ARITHMETIC','candidate_b_vectors':len(rows),'valid_triple_b':valid,'row_multiplicity_profiles':profiles,'scope':'paper arithmetic only; no graph search'}
Path(__file__).with_name('arithmetic.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
