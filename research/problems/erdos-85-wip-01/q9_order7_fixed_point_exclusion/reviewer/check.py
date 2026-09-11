from pathlib import Path
import hashlib,json
p=Path('/tmp/erdos85-sol1-q9-order7-fixed-points');o=Path(__file__).parent
for f,h in json.loads((p/'pins.json').read_text()).items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
rows=[]
for n in [78,80]:
 for f in range(n):
  m=n-f
  if m%7 or m<1+8*7:continue
  # Degrees derive directly from 9 minus whole moved7orbits.
  allowed=[d for d in range(10) if (9-d)%7==0 and d<f]
  for b in range(f+1):
   counts={2:b,9:f-b}
   if any(c and d not in allowed for d,c in counts.items()):continue
   degree_sum=sum(d*c for d,c in counts.items())
   if degree_sum%2:continue
   if sum((9-d)*c for d,c in counts.items())>m:continue
   if sum(d*(d-1)*c for d,c in counts.items())>f*(f-1):continue
   rows.append({'n':n,'fixed':f,'degree2':b,'moved_orbits':m//7})
assert rows==[{'n':78,'fixed':8,'degree2':8,'moved_orbits':10},{'n':80,'fixed':3,'degree2':3,'moved_orbits':11},{'n':80,'fixed':10,'degree2':10,'moved_orbits':10}]
assert all(r['degree2']==r['fixed'] for r in rows)
r={'status':'PASS','direct_integer_cases':rows,'scope':'Independent unreduced boundary/codegree/degree-parity inequalities; orbit argument checked on paper.'};(o/'results.json').write_text(json.dumps(r,indent=2)+'\n');(o/'input-pins.json').write_text((p/'pins.json').read_text());print(r)
