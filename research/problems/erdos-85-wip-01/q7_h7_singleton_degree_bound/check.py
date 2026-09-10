import math,json
from pathlib import Path
rows=[]
for a in range(6,10):
 for z in range(15):
  ell=49-4*a-2*z;h=14-ell-z
  if min(ell,h)<0:continue
  internal_max=min(h*(h-1)//2,(h+z)//2)
  cross_min=max(0,5*h-2*internal_max-z)
  cherries_min=None
  if ell:
   q,r=divmod(cross_min,ell);cherries_min=(ell-r)*q*(q-1)//2+r*q*(q+1)//2
  excluded=cross_min>3*ell or (cherries_min is not None and cherries_min>h*(h-1)//2)
  rows.append(dict(a=a,degree1=z,degree3=ell,degree5=h,internal_degree5_edges_upper=internal_max,cross_to_degree3_lower=cross_min,cross_cherries_lower=cherries_min,degree5_pairs=h*(h-1)//2,excluded=excluded))
Path(__file__).with_name('results.json').write_text(json.dumps({'scope':'Universal singleton degree-distribution obstruction, independent of empty incidence labels; does not exclude a whole H7 empty class.','rows':rows},indent=2)+'\n');print([r for r in rows if r['excluded']])
