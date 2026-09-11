from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;S=P.parent/'n80-m16-quotient'
pins=json.loads((S/'pins.json').read_text())
assert all(hashlib.sha256((S/f).read_bytes()).hexdigest()==h for f,h in pins.items())
source=json.loads((S/'verification.json').read_text());out=[]
for index,item in enumerate(source['representatives']):
    q=item['matrix'];bad=[]
    for i in range(5):
        if (9-q[i][i])%2 and all(q[i][j]==0 or sum(q[i][k]*q[k][j] for k in range(5))==16 for j in range(5) if i!=j):bad.append(i)
    out.append({'type':index,'obstructed_orbits':bad,'multiplicity':item['multiplicity']})
assert [r['type'] for r in out if r['obstructed_orbits']]==[2,5]
assert sum(r['multiplicity'] for r in out if r['obstructed_orbits'])==45
(P/'results.json').write_text(json.dumps({'status':'PASS','types':out,'excluded_labelled':45,'retained_labelled':165},indent=2)+'\n')
(P/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print('PASS two types/45 labelled excluded; four types/165 retained')
