import json,pathlib
src=pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
groups=json.loads((src/'groups.json').read_text());records=json.loads((src/'results.json').read_text())['records'];checked=[]
for i,(g,r) in enumerate(zip(groups,records)):
    if r['cubic_sets']:continue
    m=g['multiplication'];involutions=[x for x in range(1,24) if m[x][x]==0]
    assert involutions and all(m[x][y]==m[y][x] for x in involutions for y in range(24))
    checked.append({'group':i,'name':g['name'],'involutions':involutions,'all_central':True})
assert len(checked)==9
(pathlib.Path(__file__).parent/'central-involutions.json').write_text(json.dumps(checked,indent=2)+'\n')
