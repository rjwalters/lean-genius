import json,itertools
from pathlib import Path
out=[]
for a in range(6,10):
 for z in range(15):
  l=49-4*a-2*z;h=14-z-l
  if min(l,h)<0:continue
  feasible=False
  # Enumerate actual possible L-to-H degree histograms, avoiding Jensen's formula.
  for n3 in range(l+1):
   for n2 in range(l-n3+1):
    for n1 in range(l-n3-n2+1):
     n0=l-n3-n2-n1
     if (h<3 and n3) or (h<2 and n2) or (h<1 and n1):continue
     cross=n1+2*n2+3*n3;pairs=n2+3*n3
     if pairs>h*(h-1)//2:continue
     for m in range(h*(h-1)//2+1):
      hz=5*h-2*m-cross
      if 0<=hz<=z and 2*m<=h+hz:feasible=True
  out.append(dict(a=a,z=z,excluded=not feasible))
expected={(r['a'],r['degree1']) for r in json.loads(Path('results.json').read_text())['rows'] if r['excluded']};actual={(r['a'],r['z']) for r in out if r['excluded']};assert actual==expected=={(8,8),(9,4),(9,5),(9,6)}
Path('independent-results.json').write_text(json.dumps(out,indent=2)+'\n');print('Exact degree histogram audit agrees:',sorted(actual))
