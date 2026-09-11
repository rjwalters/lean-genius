import pathlib,json
p=pathlib.Path('/tmp/erdos85-sol1-q9-n78-six-orbit-quotients/results.json')
source=json.loads(p.read_text())
case=next(r for r in source['cases'] if r['order']==24 and r['sizes']==[6,6,6,12,24,24])
assert len(case['quotients'])==24
records=[]
for k,q in enumerate(case['quotients']):
    pairs=[(i,j) for i in range(3) for j in range(3) if i!=j and q[i][i]==2 and q[i][j]==q[j][i]==1]
    assert pairs
    records.append({'quotient':k,'two_regular_matched_orbits':pairs})
(pathlib.Path(__file__).parent/'quotient-cover.json').write_text(json.dumps(records,indent=2)+'\n')
