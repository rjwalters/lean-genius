import json
out={}
for n in (78,80):
    candidates=[]
    for f in range(13,n-57+1):
        if (n-f)%5: continue
        bs=[b for b in range(f+1) if 5*b<=n-f and f*(73-f)<=60*b]
        candidates.append({"fixed":f,"product":f*(85-f),"bound":12*n,"possible_degree4_counts":bs})
    out[n]=candidates
assert out[78]==[{"fixed":13,"product":936,"bound":936,"possible_degree4_counts":[13]}, {"fixed":18,"product":1206,"bound":936,"possible_degree4_counts":[]}]
assert all(not r["possible_degree4_counts"] for r in out[80])
assert 13*4*3==13*12 and (13*4//2)%3!=0
print(json.dumps(out,indent=2))
