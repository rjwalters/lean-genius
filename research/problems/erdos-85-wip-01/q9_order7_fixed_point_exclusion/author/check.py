import json
out={}
for n in (78,80):
    cases=[]
    for f in range(3,n-57+1):
        if (n-f)%7: continue
        bs=[b for b in range(f+1) if 7*b<=n-f and f*(73-f)<=70*b and (9*f-7*b)%2==0 and (f>=10 or b==f)]
        if bs: cases.append({"fixed":f,"degree2_counts":bs,"moved_orbits":(n-f)//7})
    out[n]=cases
assert out[78]==[{"fixed":8,"degree2_counts":[8],"moved_orbits":10}]
assert out[80]==[{"fixed":3,"degree2_counts":[3],"moved_orbits":11},{"fixed":10,"degree2_counts":[10],"moved_orbits":10}]
print(json.dumps(out,indent=2))
