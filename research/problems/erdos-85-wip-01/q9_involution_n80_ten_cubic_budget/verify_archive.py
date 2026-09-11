"""Read-only archived evidence audit; no optimizer or graph search."""
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
read=lambda f:json.loads((p/f).read_text())
pins=read('payload-pins.json')
for n,h in pins.items():assert (p/n).resolve().is_relative_to(p) and hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
for rec in read('provenance.json'):
 directory=p/rec['archive_directory']
 for n,h in json.loads((directory/rec['pin_file']).read_text()).items():assert hashlib.sha256((directory/n).read_bytes()).hexdigest()==h,n
reviews=read('accepted-reviews.json');assert {r['id'] for r in reviews}=={2250,2251} and all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in reviews)
lemma=read('cubic-ten-free-involution/results.json');assert lemma['status']=='COMPLETE' and lemma['counts']=={'binary_symmetric':32768,'row_three':112,'no_adjacent_loops':40,'two_step_bound':0}
budget=read('q9-involution-n80-ten-cubic-budget/results.json');assert budget['status']=='PASS' and budget['integer_identity_checks']==1392
cases=[]
for j in range(6):
 for n1 in range(11):
  for n2 in range(11-n1):
   for n3 in range(11-n1-n2):
    if 10+j!=15-n1-2*n2-2*n3:continue
    cross=-10+2*j+4*n3
    assert cross==-2*n1-4*n2
    if cross>=0:cases.append([j,10-n1-n2-n3,n1,n2,n3])
assert cases==budget['balanced_numerical_cases_j_n111_n211_n221_n311']==[[1,8,0,0,2],[3,9,0,0,1],[5,10,0,0,0]]
print(f'PASS: {len(pins)} payload hashes, four source/review manifests, two accepted reviews, quotient result counts and three intermediate arithmetic cases.')
